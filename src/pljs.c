#include "postgres.h"

#include "access/htup_details.h"
#include "access/table.h"
#include "access/xact.h"
#include "catalog/indexing.h"
#include "catalog/namespace.h"
#include "catalog/pg_attribute.h"
#include "catalog/pg_language.h"
#include "catalog/pg_namespace.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_type.h"
#include "catalog/pg_type_d.h"
#include "commands/trigger.h"
#include "executor/spi.h"
#include "funcapi.h"
#include "mb/pg_wchar.h"
#include "miscadmin.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/parsenodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "nodes/supportnodes.h"
#include "optimizer/optimizer.h"
#include "parser/parse_func.h"
#include "parser/parse_relation.h"
#include "parser/parse_type.h"
#include "tcop/tcopprot.h"
#include "utils/array.h"
#include "utils/builtins.h"
#include "utils/catcache.h"
#include "utils/fmgroids.h"
#include "utils/guc.h"
#include "utils/inval.h"
#include "utils/json.h"
#include "utils/lsyscache.h"
#include "utils/palloc.h"
#include "utils/regproc.h"
#include "utils/rel.h"
#include "utils/ruleutils.h"
#include "utils/snapmgr.h"
#include "utils/syscache.h"

#include "deps/quickjs/quickjs.h"
#include "windowapi.h"

#include "pljs.h"

#include <ctype.h>
#include <string.h>

#if PG_VERSION_NUM >= 180000
PG_MODULE_MAGIC_EXT(.name = "pljs", .version = PLJS_VERSION);
#else
PG_MODULE_MAGIC;
#endif

PG_FUNCTION_INFO_V1(pljs_call_handler);
PG_FUNCTION_INFO_V1(pljs_call_validator);
PG_FUNCTION_INFO_V1(pljs_inline_handler);
PG_FUNCTION_INFO_V1(pljs_source_in);
PG_FUNCTION_INFO_V1(pljs_source_out);
PG_FUNCTION_INFO_V1(pljs_call_support);
PG_FUNCTION_INFO_V1(pljs_base_type_in);
PG_FUNCTION_INFO_V1(pljs_base_type_out);

static Datum call_function(PG_FUNCTION_ARGS, pljs_context *context,
                           JSValueConst *argv);
static Datum call_srf_function(PG_FUNCTION_ARGS, pljs_context *context,
                               JSValueConst *argv);
static Datum convert_result(FunctionCallInfo fcinfo, pljs_context *context,
                            Oid rettype, JSValue ret);

static bool pljs_build_function_source(StringInfoData *src,
                                       pljs_context *context, bool is_trigger);
static void call_anonymous_function(const char *, JSContext *);
static Datum call_trigger(FunctionCallInfo fcinfo, pljs_context *context);
static Datum dispatch_call(FunctionCallInfo fcinfo);
static void run_inline(FunctionCallInfo fcinfo);
static int interrupt_handler(JSRuntime *rt, void *opaque);
static void setup_storage(pljs_storage *storage, JSContext *ctx,
                          pljs_func *function, FunctionCallInfo fcinfo);
static JSValue js_throw_uncatchable(ErrorData *edata, JSContext *ctx);
static void pljs_run_with_storage(JSContext *ctx, pljs_func *function,
                                  FunctionCallInfo fcinfo, bool own_spi,
                                  void (*run)(void *), void *arg);
static void pljs_raise_if_ending(void);
static bool pljs_argmode_is_input(char argmode);
static void pljs_reset_all_stamped_procs(void);

/** \brief QuickJS Runtime */
JSRuntime *rt = NULL;

/** \brief PLJS Configuration */
pljs_configuration configuration = {0};

// class id for prepared statement handles.
JSClassID js_prepared_statement_handle_id;

// class id for cursor handles.
JSClassID js_cursor_handle_id;

// class id for pljs storage
JSClassID js_pljs_storage_id;

// class id for pljs window object
JSClassID js_window_id;

/*
 * The storage of the pljs call running now -- a function, trigger or DO block
 * -- or NULL outside of one; see pljs_current_storage().
 */
static pljs_storage *current_storage = NULL;
static JSContext *current_compiling_ctx = NULL;

bool pljs_context_is_active(JSContext *ctx) {
  if (ctx == NULL) {
    return false;
  }
  if (ctx == current_compiling_ctx) {
    return true;
  }
  for (pljs_storage *s = current_storage; s != NULL; s = s->previous) {
    if (s->ctx == ctx) {
      return true;
    }
  }
  return false;
}

/*
 * The error the running call has to end with, or NULL; see
 * pljs_throw_fatal_error().
 */
static ErrorData *pljs_fatal_error(void) {
  return current_storage != NULL ? current_storage->fatal_error : NULL;
}

/*
 * Whether a function's result is being converted, anywhere up the stack; see
 * pljs_commit().
 */
bool pljs_converting_result = false;
bool pljs_preserve_numeric_precision = false;
bool pljs_pass_user_types_as_bytes = false;

/**
 * @brief Creates and configures the QuickJS runtime.
 *
 * Everything a runtime needs before any JSContext is created in it is set
 * here, so the runtime pljs_reset() replaces is set up the same way as the
 * one _PG_init() created.
 */
void pljs_runtime_init(void) {
  rt = JS_NewRuntime();

  /*
   * Bound the JS call-stack budget explicitly instead of trusting the vendored
   * JS_DEFAULT_STACK_SIZE.  Without an active limit, unbounded/deep JS
   * recursion runs the backend's C stack into the ground and crashes the whole
   * process (SIGSEGV) rather than raising a catchable "stack overflow".  We
   * size the JS budget to half of the DBA's max_stack_depth so pure-JS
   * recursion trips QuickJS's guard well before PostgreSQL's own C-stack limit
   * (and long before the kernel stack limit) is reached, with a floor so a
   * small max_stack_depth still leaves JS usable.  PostgreSQL's own
   * check_stack_depth() bounds any cumulative C stack consumed across nested
   * JS<->SQL re-entries.
   *
   * The budget set here is a size, not an anchor: JS_NewRuntime() records the
   * stack top at this point in _PG_init, which is not where any real JS call
   * begins.  Each entry into JS therefore calls JS_UpdateStackTop() to
   * re-anchor the measurement at its own depth -- see the call sites around
   * each JS_Call().
   *
   * Note an asymmetry with pljs.memory_limit below, which does install an
   * assign hook: max_stack_depth is read once, here, so a later SET
   * max_stack_depth does not change the JS budget for the life of the backend.
   * It is a core GUC with no hook available to us, and re-reading it per call
   * would let one session's SET silently resize a runtime shared with every
   * other function in the backend.
   */
  {
    long depth_bytes = (long)max_stack_depth * 1024L;
    size_t js_stack_size = (size_t)(depth_bytes / 2);
    if (js_stack_size < 256 * 1024) {
      js_stack_size = 256 * 1024;
    }
    JS_SetMaxStackSize(rt, js_stack_size);
  }

  /*
   * Stop JavaScript for a cancel or a termination; see interrupt_handler().
   * Here, once, rather than before each call: a new backend's pljs.start_proc
   * and a function's top-level code both run before any call, and ran with no
   * handler at all, so a statement_timeout never stopped them, and nor did
   * pg_terminate_backend().
   */
  JS_SetInterruptHandler(rt, interrupt_handler, NULL);

  // Register runtime JS classes (must happen before any JSContext is created,
  // so every context sees the class; e.g. the prepared-statement handle whose
  // finalizer reclaims otherwise-leaked SPI plans).
  pljs_register_js_classes(rt);

  // Set up a memory limit if it exists.
  if (configuration.memory_limit) {
    JS_SetMemoryLimit(rt, configuration.memory_limit * 1024 * 1024);
  }

  // Stored modules are loaded through QuickJS's module system.
  JS_SetModuleLoaderFunc(rt, pljs_module_normalize, pljs_module_loader, NULL);

  // Initialize hook JS classes.
  pljs_hooks_init(rt);
}

static uint64 pljs_catalog_gen = 1;
static Oid pljs_cached_holder_relid = InvalidOid;
static bool pljs_in_internal_catalog_update = false;

uint64 pljs_get_catalog_gen(void) { return pljs_catalog_gen; }

static void pljs_catalog_inval_cb(Datum arg, Oid relid) {
  if (!pljs_in_internal_catalog_update &&
      (relid == InvalidOid || relid != pljs_cached_holder_relid)) {
    pljs_catalog_gen++;
  }
}

static void pljs_catalog_xact_cb(XactEvent event, void *arg) {
  if (event == XACT_EVENT_ABORT || event == XACT_EVENT_PARALLEL_ABORT) {
    pljs_catalog_gen++;
  }
  pljs_fdw_xact_cb(event, arg);
}

static void pljs_catalog_subxact_cb(SubXactEvent event,
                                    SubTransactionId mySubid,
                                    SubTransactionId parentSubid, void *arg) {
  if (event == SUBXACT_EVENT_ABORT_SUB) {
    pljs_catalog_gen++;
  }
}

/**
 * @brief PostgreSQL extension initialization function.
 *
 * Initialize the extension, setting up the cache, GUCs, and QuickJS
 * runtime.
 */
void _PG_init(void) {
  // NB: do NOT install our own signal() handlers here.  This runs inside a
  // backend that has already set up PostgreSQL's own SIGINT/SIGTERM handlers
  // (query cancel, fast shutdown); overwriting them process-wide broke
  // statement_timeout / pg_cancel_backend / pg_terminate_backend for the whole
  // backend for the rest of its life.  Instead, interrupt_handler() consults
  // PostgreSQL's interrupt flags directly (see below).

  // Initialize cache.
  pljs_cache_init();

  // Initialize what the type conversions keep for the life of the backend.
  pljs_type_io_init();

  // Initialize the GUCs.
  pljs_guc_init();

  // Set up the quickjs runtime.
  pljs_runtime_init();

  // Notice changes to the module tables.
  pljs_modules_init();

  // Track external relation/catalog invalidations and transaction aborts.
  CacheRegisterRelcacheCallback(pljs_catalog_inval_cb, (Datum)0);
  RegisterXactCallback(pljs_catalog_xact_cb, NULL);
  RegisterSubXactCallback(pljs_catalog_subxact_cb, NULL);

  // Install hook callbacks.
  pljs_hooks_install();
}

/**
 * GUC check callbacks for hook-related GUCs.
 *
 * Without shared_preload_libraries, PGC_SUSET is not enforced for GUC
 * placeholders set before the library loads. These check callbacks reject
 * non-superuser attempts from interactive sources (SET command), closing
 * the security gap where a non-superuser could set hook GUCs as
 * placeholders that later take effect for superuser queries.
 */
static bool pljs_hook_bool_check(bool *newval, void **extra,
                                 GucSource source) {
  if (*newval && source >= PGC_S_INTERACTIVE && !superuser()) {
    GUC_check_errmsg("permission denied to set hook parameter");
    GUC_check_errhint("Must be superuser to enable PLJS hooks.");
    return false;
  }
  return true;
}

static bool pljs_hook_int_check(int *newval, void **extra, GucSource source) {
  if (source >= PGC_S_INTERACTIVE && !superuser()) {
    GUC_check_errmsg("permission denied to set hook parameter");
    GUC_check_errhint("Must be superuser to configure PLJS hooks.");
    return false;
  }
  return true;
}

static bool pljs_hook_string_check(char **newval, void **extra,
                                   GucSource source) {
  if (*newval && (*newval)[0] != '\0' && source >= PGC_S_INTERACTIVE &&
      !superuser()) {
    GUC_check_errmsg("permission denied to set hook parameter");
    GUC_check_errhint("Must be superuser to configure PLJS hooks.");
    return false;
  }
  return true;
}

/**
 * @brief Assign hook for pljs.memory_limit.
 *
 * Re-applies the limit to the live QuickJS runtime when the GUC is changed at
 * runtime (SET pljs.memory_limit = ...).  Without this the GUC value changed
 * but the interpreter kept whatever limit was installed in _PG_init (the value
 * present when pljs was first loaded), so a runtime SET silently had no effect
 * and could not be used to contain a misbehaving function in a running backend.
 * At initial GUC definition (boot value) rt is still NULL, so this is a no-op
 * then and _PG_init installs the load-time value explicitly.
 */
static void pljs_assign_memory_limit(int newval, void *extra) {
  if (rt != NULL && newval > 0) {
    JS_SetMemoryLimit(rt, (size_t)newval * 1024 * 1024);
  }
}

static void pljs_assign_max_cached_contexts(int newval, void *extra) {
  if (newval > 0) {
    pljs_cache_evict_excess(newval);
  }
}

/**
 * @brief Set up the GUCs.
 *
 * Sets up the GUCs that help define the behavior of the interpreter.
 */
void pljs_guc_init(void) {
#ifdef EXECUTION_TIMEOUT
  DefineCustomIntVariable(
      "pljs.execution_timeout", gettext_noop("Javascriot execution timeout."),
      gettext_noop(
          "The default value is 300 seconds."
          "This allows you to override the default execution timeout."),
      &configuration.execution_timeout, 300, 1, 65536, PGC_USERSET, 0, NULL,
      NULL, NULL);
#endif

  DefineCustomIntVariable("pljs.memory_limit",
                          gettext_noop("Runtime limit in MBytes"),
                          gettext_noop("The default value is 512 MB"),
                          (int *)&configuration.memory_limit, 512, 64, 3096,
                          PGC_SUSET, 0, NULL, pljs_assign_memory_limit, NULL);

  DefineCustomStringVariable(
      "pljs.start_proc",
      gettext_noop("PLJS function to run once when PLJS is first used."), NULL,
      &configuration.start_proc, NULL, PGC_USERSET, 0, NULL, NULL, NULL);

  DefineCustomBoolVariable(
      "pljs.hooks_enabled",
      gettext_noop("Enable PLJS executor hooks."),
      gettext_noop("When enabled, PLJS will install executor hooks that allow "
                   "JavaScript functions to intercept query execution. "
                   "Requires superuser to enable."),
      &configuration.hooks_enabled, false, PGC_SUSET, 0,
      pljs_hook_bool_check, NULL, NULL);

  DefineCustomIntVariable(
      "pljs.hooks_max_depth",
      gettext_noop("Maximum recursion depth for PLJS hooks."),
      gettext_noop("Limits how deeply hooks can recurse when a hook "
                   "function triggers the same hook via pljs.execute(). "
                   "Requires superuser to change."),
      &configuration.hooks_max_depth, 5, 1, 64, PGC_SUSET, 0,
      pljs_hook_int_check, NULL, NULL);

  DefineCustomIntVariable(
      "pljs.max_module_depth",
      gettext_noop("Maximum recursion depth for nested module imports."),
      gettext_noop("Limits how deeply pljs.import()/pljs.require() calls "
                   "can nest before an error is raised. Guards against "
                   "runaway recursion via circular dependencies."),
      &configuration.max_module_depth, 512, 1, 65536, PGC_USERSET, 0, NULL,
      NULL, NULL);

  DefineCustomIntVariable(
      "pljs.max_cached_contexts",
      gettext_noop("Maximum number of cached JavaScript contexts per backend."),
      gettext_noop("When this limit is reached, the least-recently-used "
                   "inactive context is evicted before a new one is cached."),
      &configuration.max_cached_contexts, 64, 1, 1024, PGC_SUSET, 0, NULL,
      pljs_assign_max_cached_contexts, NULL);

  DefineCustomBoolVariable(
      "pljs.allow_raw_user_types",
      gettext_noop("Allow passing user-defined base types (TYPCATEGORY_USER) "
                   "as raw Uint8Array byte buffers."),
      gettext_noop("Restricted to superuser-owned functions/handlers with "
                   "pass_user_types_as_bytes enabled."),
      &configuration.allow_raw_user_types, false, PGC_SUSET, 0,
      pljs_hook_bool_check, NULL, NULL);

  // Hook GUCs - each names a PLJS function to call for the given hook.
  // All require superuser and pljs.hooks_enabled = true at runtime.
  DefineCustomStringVariable(
      "pljs.executor_start_hook",
      gettext_noop("PLJS function to call on ExecutorStart."), NULL,
      &configuration.hook_executor_start, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.executor_run_hook",
      gettext_noop("PLJS function to call on ExecutorRun."), NULL,
      &configuration.hook_executor_run, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.executor_end_hook",
      gettext_noop("PLJS function to call on ExecutorEnd."), NULL,
      &configuration.hook_executor_end, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.planner_hook",
      gettext_noop("PLJS function to call on planner."), NULL,
      &configuration.hook_planner, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.create_upper_paths_hook",
      gettext_noop("PLJS function to call on create_upper_paths."), NULL,
      &configuration.hook_create_upper_paths, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.set_rel_pathlist_hook",
      gettext_noop("PLJS function to call on set_rel_pathlist."), NULL,
      &configuration.hook_set_rel_pathlist, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.set_join_pathlist_hook",
      gettext_noop("PLJS function to call on set_join_pathlist."), NULL,
      &configuration.hook_set_join_pathlist, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.join_search_hook",
      gettext_noop("PLJS function to call on join_search."), NULL,
      &configuration.hook_join_search, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.get_relation_info_hook",
      gettext_noop("PLJS function to call on get_relation_info."), NULL,
      &configuration.hook_get_relation_info, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.needs_fmgr_hook",
      gettext_noop("PLJS function to call on needs_fmgr."), NULL,
      &configuration.hook_needs_fmgr, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.fmgr_hook",
      gettext_noop("PLJS function to call on fmgr."), NULL,
      &configuration.hook_fmgr, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.object_access_hook",
      gettext_noop("PLJS function to call on object_access."), NULL,
      &configuration.hook_object_access, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.object_access_hook_str",
      gettext_noop("PLJS function to call on object_access_hook_str."), NULL,
      &configuration.hook_object_access_str, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);

  DefineCustomStringVariable(
      "pljs.emit_log_hook",
      gettext_noop("PLJS function to call on emit_log."), NULL,
      &configuration.hook_emit_log, NULL, PGC_SUSET, 0,
      pljs_hook_string_check, NULL, NULL);
}

/**
 * @brief Converts a Javascript error into a string.
 *
 * Takes a javascript context and converts it into a string,
 * allocating the memory needed in the currect memory context.
 *
 * @param ctx #JSContext - Javascript context with the error
 * @returns @c char * as an error message
 */
/*
 * Extract the current JavaScript exception.
 *
 * Returns a palloc'd string suitable for errdetail(): the stringified error
 * followed by its stack trace.  When message_out is non-NULL it is set to a
 * palloc'd copy of the error's own `message` property (or the stringified
 * throw value for non-Error throws), so callers can surface that as the
 * primary errmsg() the way plv8 does, instead of a generic "execution error".
 * Preserving the message here is what lets a coded error (e.g. the "[CODE] "
 * prefix embedded by the mirror procedures) survive across a nested
 * pljs.execute()/SPI boundary.
 *
 * sqlstate_out is set the same way from the error's `sqlstate` property, so a
 * PostgreSQL error that passed through JavaScript is re-raised under its own
 * SQLSTATE instead of collapsing to XX000.
 */
/*
 * Reads a property of a thrown error as a palloc'd string, or NULL if it has
 * none.  A getter that throws, or a value whose toString() does, is taken for
 * none, and its exception released: it was left pending in the context, and
 * kept what it threw alive until the next exception replaced it.
 */
static char *dump_error_property(JSContext *ctx, JSValueConst error,
                                 const char *name) {
  JSValue value = JS_GetPropertyStr(ctx, error, name);
  const char *str;
  char *ret;

  if (JS_IsException(value)) {
    JS_FreeValue(ctx, JS_GetException(ctx));
    return NULL;
  }

  if (JS_IsUndefined(value)) {
    return NULL;
  }

  str = JS_ToCString(ctx, value);
  JS_FreeValue(ctx, value);

  if (str == NULL) {
    JS_FreeValue(ctx, JS_GetException(ctx));
    return NULL;
  }

  ret = pstrdup(str);
  JS_FreeCString(ctx, str);

  return ret;
}

typedef struct pljs_js_error_info {
  char *message;
  char *pg_detail;
  char *detail;
  char *hint;
  char *schema_name;
  char *table_name;
  char *column_name;
  char *datatype_name;
  char *constraint_name;
  int sqlerrcode;
} pljs_js_error_info;

static int pljs_parse_sqlerrcode(JSContext *ctx, JSValueConst val) {
  if (JS_IsNumber(val)) {
    int32_t code = 0;
    if (JS_ToInt32(ctx, &code, val) == 0 && code != 0) {
      return (int)code;
    }
    return 0;
  }

  if (JS_IsString(val)) {
    const char *s = JS_ToCString(ctx, val);
    if (s == NULL) {
      JS_FreeValue(ctx, JS_GetException(ctx));
      return 0;
    }

    int code = 0;
    if (strlen(s) == 5) {
      bool valid = true;
      char c[5];
      for (int i = 0; i < 5; i++) {
        unsigned char ch = (unsigned char)s[i];
        if (ch >= 'a' && ch <= 'z') {
          ch = (unsigned char)(ch - 'a' + 'A');
        }
        if (!((ch >= '0' && ch <= '9') || (ch >= 'A' && ch <= 'Z'))) {
          valid = false;
          break;
        }
        c[i] = (char)ch;
      }
      if (valid) {
        code = MAKE_SQLSTATE(c[0], c[1], c[2], c[3], c[4]);
      }
    }

    JS_FreeCString(ctx, s);
    return code;
  }

  return 0;
}

static char *dump_error_ex(JSContext *ctx, pljs_js_error_info *info) {
  JSValue exception_val, val;
  const char *stack;
  const char *str;
  bool is_error;
  bool is_obj;
  char *ret = NULL;
  size_t s1, s2;

  if (info) {
    memset(info, 0, sizeof(*info));
    info->sqlerrcode = ERRCODE_INTERNAL_ERROR;
  }

  exception_val = JS_GetException(ctx);

  /* In the case of OOM, a null exception is thrown. */
  if (JS_IsNull(exception_val)) {
    char *oom = palloc(14);
    strcpy(oom, "out of memory");

    if (info) {
      info->message = pstrdup("out of memory");
      info->detail = oom;
    }

    JS_FreeValue(ctx, exception_val);

    return oom;
  }

  is_error = JS_IsError(ctx, exception_val);
  is_obj = JS_IsObject(exception_val);
  str = JS_ToCStringLen(ctx, &s1, exception_val);

  if (!str) {
    elog(DEBUG3, "error thrown but no error message");

    /*
     * The thrown value's toString() threw in turn.  Release that exception as
     * well as the thrown value, rather than leave it pending in the context.
     */
    JS_FreeValue(ctx, JS_GetException(ctx));
    JS_FreeValue(ctx, exception_val);

    return NULL;
  }

  if (info && is_obj) {
    char *detail = dump_error_property(ctx, exception_val, "detail");
    if (detail && detail[0]) {
      info->pg_detail = detail;
    }

    char *hint = dump_error_property(ctx, exception_val, "hint");
    if (hint && hint[0]) {
      info->hint = hint;
    }

    char *schema_name = dump_error_property(ctx, exception_val, "schema_name");
    if (schema_name && schema_name[0]) {
      info->schema_name = schema_name;
    }

    char *table_name = dump_error_property(ctx, exception_val, "table_name");
    if (table_name && table_name[0]) {
      info->table_name = table_name;
    }

    char *column_name = dump_error_property(ctx, exception_val, "column_name");
    if (column_name && column_name[0]) {
      info->column_name = column_name;
    }

    char *datatype_name =
        dump_error_property(ctx, exception_val, "datatype_name");
    if (datatype_name && datatype_name[0]) {
      info->datatype_name = datatype_name;
    }

    char *constraint_name =
        dump_error_property(ctx, exception_val, "constraint_name");
    if (constraint_name && constraint_name[0]) {
      info->constraint_name = constraint_name;
    }

    static const char *const code_keys[] = {"code", "sqlerrcode", "sqlstate"};
    for (int i = 0; i < 3; i++) {
      JSValue cval = JS_GetPropertyStr(ctx, exception_val, code_keys[i]);
      if (JS_IsException(cval)) {
        JS_FreeValue(ctx, JS_GetException(ctx));
        continue;
      }
      int parsed = pljs_parse_sqlerrcode(ctx, cval);
      JS_FreeValue(ctx, cval);
      if (parsed != 0) {
        info->sqlerrcode = parsed;
        break;
      }
    }
  }

  if (info) {
    /*
     * Prefer the Error's or object's own `message` property; fall back to the
     * stringified throw value for non-object throws or a missing/empty message.
     */
    if (is_obj) {
      char *message = dump_error_property(ctx, exception_val, "message");

      if (message && message[0]) {
        info->message = message;
      }
    }

    if (info->message == NULL) {
      info->message = pstrdup(str);
    }
  }

  if (!is_error) {
    ret = (char *)palloc((s1 + 8) * sizeof(char));
    sprintf(ret, "Throw:\n%s", str);
  } else {
    val = JS_GetPropertyStr(ctx, exception_val, "stack");

    /*
     * A `stack` that cannot be made a string -- a Symbol, or a getter that
     * throws -- is treated as no stack at all.  Its NULL went to sprintf(),
     * which wrote "(null)" past the end of a buffer sized for an empty stack.
     */
    stack = JS_IsUndefined(val) ? NULL : JS_ToCStringLen(ctx, &s2, val);

    if (stack != NULL) {
      ret = (char *)palloc((s1 + s2 + 2) * sizeof(char));
      sprintf(ret, "%s\n%s", str, stack);
      JS_FreeCString(ctx, stack);
    } else if (!JS_IsUndefined(val)) {
      JS_FreeValue(ctx, JS_GetException(ctx));
    }

    JS_FreeValue(ctx, val);
  }

  if (info) {
    info->detail = ret;
  }

  JS_FreeCString(ctx, str);
  JS_FreeValue(ctx, exception_val);

  return ret;
}

/**
 * @brief Extract the current JavaScript exception as an error string.
 *
 * The exported form of dump_error(), for hooks.c and for companion
 * extensions, which have no use for the error's message, detail or SQLSTATE
 * on their own.
 *
 * @param ctx #JSContext - Javascript context with the error
 * @returns @c char * as an error message
 */
char *pljs_dump_error(JSContext *ctx) {
  return dump_error_ex(ctx, NULL);
}

pg_noreturn static void pljs_ereport_js_error_info(
    const pljs_js_error_info *info, const char *fallback) {
  int sqlerrcode =
      (info && info->sqlerrcode != 0) ? info->sqlerrcode : ERRCODE_INTERNAL_ERROR;
  const char *emessage =
      (info && info->message && info->message[0]) ? info->message : fallback;
  const char *edetail = (info && info->pg_detail && info->pg_detail[0])
                            ? info->pg_detail
                            : (info ? info->detail : NULL);
  const char *ehint = (info && info->hint && info->hint[0]) ? info->hint : NULL;
  const char *eschema =
      (info && info->schema_name && info->schema_name[0]) ? info->schema_name : NULL;
  const char *etable =
      (info && info->table_name && info->table_name[0]) ? info->table_name : NULL;
  const char *ecolumn =
      (info && info->column_name && info->column_name[0]) ? info->column_name : NULL;
  const char *edatatype = (info && info->datatype_name && info->datatype_name[0])
                              ? info->datatype_name
                              : NULL;
  const char *econstraint =
      (info && info->constraint_name && info->constraint_name[0])
          ? info->constraint_name
          : NULL;
  ErrorData *fatal_error = pljs_fatal_error();

  /* The exception stood for this error; see pljs_throw_fatal_error(). */
  if (fatal_error != NULL) {
    ReThrowError(fatal_error);
  }

  /*
   * What JavaScript wrote is UTF-8, and a message in another database
   * encoding had every accented letter as the two bytes of its UTF-8.  Never
   * raising, which would replace the error being reported; see
   * pljs_utf8_to_server_lossy().
   */
  emessage = pljs_utf8_to_server_lossy(emessage, strlen(emessage));

  if (edetail == NULL) {
    edetail = fallback;
  }

  edetail = pljs_utf8_to_server_lossy(edetail, strlen(edetail));

  if (ehint != NULL) {
    ehint = pljs_utf8_to_server_lossy(ehint, strlen(ehint));
  }
  if (eschema != NULL) {
    eschema = pljs_utf8_to_server_lossy(eschema, strlen(eschema));
  }
  if (etable != NULL) {
    etable = pljs_utf8_to_server_lossy(etable, strlen(etable));
  }
  if (ecolumn != NULL) {
    ecolumn = pljs_utf8_to_server_lossy(ecolumn, strlen(ecolumn));
  }
  if (edatatype != NULL) {
    edatatype = pljs_utf8_to_server_lossy(edatatype, strlen(edatatype));
  }
  if (econstraint != NULL) {
    econstraint = pljs_utf8_to_server_lossy(econstraint, strlen(econstraint));
  }

  ereport(
      ERROR,
      (errcode(sqlerrcode), errmsg("%s", emessage), errdetail("%s", edetail),
       ehint ? errhint("%s", ehint) : 0,
       eschema ? err_generic_string(PG_DIAG_SCHEMA_NAME, eschema) : 0,
       etable ? err_generic_string(PG_DIAG_TABLE_NAME, etable) : 0,
       ecolumn ? err_generic_string(PG_DIAG_COLUMN_NAME, ecolumn) : 0,
       edatatype ? err_generic_string(PG_DIAG_DATATYPE_NAME, edatatype) : 0,
       econstraint ? err_generic_string(PG_DIAG_CONSTRAINT_NAME, econstraint)
                   : 0));
  pg_unreachable();
}

/**
 * @brief Raises the pending JavaScript exception as a PostgreSQL error.
 *
 * For C code that finds a QuickJS call has failed because JavaScript threw --
 * a getter, toString() or valueOf() run while a value was being converted --
 * and has to raise rather than hand the exception back to JavaScript.  The
 * error keeps the exception's message, and its SQLSTATE if it wrapped a
 * PostgreSQL error.
 *
 * @param ctx #JSContext - the context with the pending exception
 */
void pljs_ereport_js_exception(JSContext *ctx) {
  pljs_js_error_info errinfo;
  dump_error_ex(ctx, &errinfo);

  /*
   * The exception can be QuickJS's "interrupted", thrown for a pending cancel
   * or termination -- a statement_timeout while a getter or toString() ran
   * for a conversion.  Raise the real error, as the call paths do, so it
   * keeps its SQLSTATE rather than becoming an internal error.
   */
  CHECK_FOR_INTERRUPTS();

  pljs_ereport_js_error_info(&errinfo, "could not convert a JavaScript value");
}

static int interrupt_handler(JSRuntime *rt, void *opaque) {
  /*
   * Return non-zero to make QuickJS abort the running script.  We interrupt on
   * a pending query cancel (statement_timeout, pg_cancel_backend) or backend
   * termination (pg_terminate_backend, fast shutdown), read straight from
   * PostgreSQL's own interrupt flags.
   *
   * We deliberately do NOT call CHECK_FOR_INTERRUPTS() here: that would
   * ereport(ERROR) / siglongjmp out of the middle of the QuickJS interpreter
   * and leave the runtime in an inconsistent state.  Instead we let QuickJS
   * unwind cleanly to a JS exception, and each caller runs
   * CHECK_FOR_INTERRUPTS() once control is back in C to raise the real error
   * (see the JS_IsException paths below).
   */
  /*
   * Only the flags that mean "this query must stop": a cancel, a backend
   * termination, or a lost client.  A recovery conflict sets one of the first
   * two itself.  InterruptPending is deliberately NOT consulted: PostgreSQL
   * sets it for many things that do not end the query -- a sinval catchup, a
   * ProcSignal barrier, pg_log_backend_memory_contexts(), a NOTIFY wake-up --
   * and once QuickJS has aborted the script there is no way back: the caller's
   * CHECK_FOR_INTERRUPTS() handles the benign interrupt and returns, and the
   * function then fails with "interrupted" for no reason.  With
   * InterruptPending in the condition, pg_object_keys_leak failed on every run
   * on PostgreSQL 18 and any long-running pljs function died when another
   * session called pg_log_backend_memory_contexts() on it.
   *
   * A call that has to end with an error stops too, should C code have caught
   * the exception that was to end it; see pljs_throw_fatal_error().
   */
  return (QueryCancelPending || ProcDiePending || ClientConnectionLost ||
          pljs_fatal_error() != NULL)
             ? 1
             : 0;
}

/**
 * @brief Set up the pljs_context.
 *
 * Sets up the pljs_context with the function and any needed contexts.
 *
 * @param fcinfo #FunctionCallInfo - optional, allows for the `fn_oid` to be
 * added
 * @param proctuple #HeapTuple - information pointer for the source and
 * argument information
 * @param context #pljs_context - context to set up the function into
 * @returns @c bool of success for failure
 */
static bool setup_function(FunctionCallInfo fcinfo, HeapTuple proctuple,
                           pljs_context *context) {
  Datum prosrcdatum;
  bool isnull;
  Form_pg_proc pg_proc_entry = NULL;
  pljs_func *pljs_function = NULL;
  char **arguments = NULL;
  Oid *argtypes = NULL;
  char *argmodes;
  int nargs;

  // Search for the system cache entry for the source of the procedure.
  prosrcdatum =
      SysCacheGetAttr(PROCOID, proctuple, Anum_pg_proc_prosrc, &isnull);

  // If we fail, all is lost already, might as well give up hope.
  if (isnull) {
    ereport(ERROR, errcode(ERRCODE_INTERNAL_ERROR),
            errmsg("unable to find prosrc"));

    return false;
  }

  pljs_encoding_init();

  pljs_function = palloc0(sizeof(pljs_func));

  // Make a UTF-8 copy of the source available for later transpilation and
  // compilation.
  char *prosrc = DatumGetCString(DirectFunctionCall1(textout, prosrcdatum));
  pljs_function->prosrc = pljs_server_to_utf8(prosrc, strlen(prosrc));
  if (pljs_function->prosrc != prosrc) {
    pfree(prosrc);
  }

  /*
   * Record which pg_proc tuple this was compiled from.  CREATE OR REPLACE
   * writes a new tuple version, so a cached entry whose xmin/tid no longer
   * match the current tuple was compiled from a body that no longer exists.
   * These two fields were already declared in pljs_func but never written or
   * read.
   */
  pljs_function->fn_xmin = HeapTupleHeaderGetRawXmin(proctuple->t_data);
  pljs_function->fn_tid = proctuple->t_self;

  pg_proc_entry = (Form_pg_proc)GETSTRUCT(proctuple);

  // Get the actual name of the procedure.
  memcpy(pljs_function->proname, NameStr(pg_proc_entry->proname), NAMEDATALEN);

  // Are we building a set-returning function?  If so, a special case.
  pljs_function->is_srf = pg_proc_entry->proretset;

  // Figure out the return type, we care about this when we are calling
  // directly from postgres.
  if (fcinfo && IsPolymorphicType(pg_proc_entry->prorettype)) {
    pljs_function->rettype = get_fn_expr_rettype(fcinfo->flinfo);
  } else {
    pljs_function->rettype = pg_proc_entry->prorettype;
  }

  // Get all of the argument information.
  nargs = get_func_arg_info(proctuple, &argtypes, &arguments, &argmodes);

  int inargs = 0;
  for (int i = 0; i < nargs; i++) {
    Oid argtype = argtypes[i];
    char argmode = argmodes ? argmodes[i] : PROARGMODE_IN;

    // Get a UTF-8 copy of the arguments themselves, we use them for creating
    // the function.
    if (arguments && arguments[i]) {
      char *argname = pljs_server_to_utf8(arguments[i], strlen(arguments[i]));
      if (argname != arguments[i]) {
        pfree(arguments[i]);
      }
      context->arguments[i] = argname;
    } else {
      context->arguments[i] = NULL;
    }

    // We differentiate input arguments from output only.
    if (pljs_argmode_is_input(argmode)) {
      /*
       * Resolve polymorphic types, if this is an actual call context.  By the
       * input argument's place in the call, which has no OUT arguments; see
       * pljs_resolve_argtype().
       */
      if (fcinfo && IsPolymorphicType(argtype)) {
        argtype = get_fn_expr_argtype(fcinfo->flinfo, inargs);
      }

      /*
       * By its place in the call, as a window object's methods ask for one;
       * see pljs_window_arg_type().  It was kept by its place among all of
       * the arguments, and an OUT argument before it moved it.
       */
      pljs_function->argtypes[inargs] = argtype;
      inargs++;
    }

    pljs_function->argmodes[i] = argmode;
  }

  pljs_function->inargs = inargs;
  pljs_function->nargs = nargs;

  context->function = pljs_function;

  // Functions are scoped to the effective user and function owner pair.
  context->function->user_id = GetUserId();
  context->function->owner_id = pg_proc_entry->proowner;

  // If we have the function call info, we set the function OID.
  if (fcinfo) {
    context->function->fn_oid = fcinfo->flinfo->fn_oid;
  } else {
    context->function->fn_oid = pg_proc_entry->oid;
  }

  return true;
}

/**
 * @brief Check to see if there is permission to execute a function.
 *
 * Searches the catalog for a function and checks to see if the current user
 * has permission to execute it.
 *
 * @param signature @c char *
 * @returns @c bool
 */
bool pljs_has_permission_to_execute(const char *signature) {
  // Stack-allocate FunctionCallInfoBaseData with
  // space for 2 arguments:
  LOCAL_FCINFO(fake_fcinfo, 2);

  FmgrInfo flinfo;

  char perm[16];
  strcpy(perm, "EXECUTE");
  text *arg = (text *)palloc(8 + VARHDRSZ);
  memcpy(VARDATA(arg), perm, 8);
  SET_VARSIZE(arg, 8 + VARHDRSZ);
  Oid funcoid;

  if (strchr(signature, '(') == NULL) {
    funcoid = DatumGetObjectId(
        DirectFunctionCall1(regprocin, CStringGetDatum(signature)));
  } else {
    funcoid = DatumGetObjectId(
        DirectFunctionCall1(regprocedurein, CStringGetDatum(signature)));
  }

  MemSet(&flinfo, 0, sizeof(flinfo));
  fake_fcinfo->flinfo = &flinfo;
  flinfo.fn_oid = InvalidOid;
  flinfo.fn_mcxt = CurrentMemoryContext;
  fake_fcinfo->nargs = 2;
  fake_fcinfo->args[0].value = ObjectIdGetDatum(funcoid);
  fake_fcinfo->args[1].value = PointerGetDatum(arg);

  Datum ret = has_function_privilege_id(fake_fcinfo);

  if (ret == 0) {
    elog(WARNING, "failed to find or no permission for js function %s",
         signature);
    return false;
  } else {
    return true;
  }
}

/**
 * @brief Validates and runs the `pljs.start_proc` if there is one.
 *
 * Finds, verifies, and executes a `pljs.start_proc` if one is set.
 * This is executed whenever a new context is created.
 */
/* What pljs_run_with_storage() runs for setup_start_proc(). */
typedef struct pljs_start_proc_run {
  JSContext *ctx;
  JSValue func;
} pljs_start_proc_run;

/**
 * @brief Calls the pljs.start_proc; see setup_start_proc().
 *
 * @param arg #pljs_start_proc_run - the context and the function, which is
 * released
 */
static void run_start_proc(void *arg) {
  pljs_start_proc_run *run = (pljs_start_proc_run *)arg;
  JSValue ret = JS_Call(run->ctx, run->func, JS_UNDEFINED, 0, NULL);

  if (JS_IsException(ret)) {
    pljs_js_error_info errinfo;
    dump_error_ex(run->ctx, &errinfo);

    /*
     * Release the JavaScript side before reporting: the report does not
     * return, so anything freed after it is never freed at all.
     */
    JS_FreeValue(run->ctx, ret);
    JS_FreeValue(run->ctx, run->func);

    /* Surface a pending cancel/terminate as the real PostgreSQL error. */
    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "start proc execution error");
  }

  /*
   * The function reference and the call's result both belong to this
   * function. Neither was released, so every context creation with
   * pljs.start_proc set leaked both.
   */
  JS_FreeValue(run->ctx, ret);
  JS_FreeValue(run->ctx, run->func);
}

static void setup_start_proc(JSContext *ctx) {
  pljs_start_proc_run run = {.ctx = ctx, .func = JS_UNDEFINED};
  volatile Oid funcoid = InvalidOid;

  // Get a copy of the current memory context, we will need to switch to it in
  // case of an error.
  MemoryContext memory_context = CurrentMemoryContext;

  /*
   * A start_proc that cannot be found, or that the user may not run, is
   * warned of.  Only finding it: compiling it runs any code at the top level
   * of its source, and an error there -- a statement_timeout included --
   * was taken for a failure to find it, logged, and forgotten, and the
   * statement ran on past its timeout.  It raises as running it does.
   */
  PG_TRY();
  {
    // Check to see if we have permission to execute the startup procedure
    if (pljs_has_permission_to_execute(configuration.start_proc)) {
      if (strchr(configuration.start_proc, '(') == NULL) {
        funcoid = DatumGetObjectId(DirectFunctionCall1(
            regprocin, CStringGetDatum(configuration.start_proc)));
      } else {
        funcoid = DatumGetObjectId(DirectFunctionCall1(
            regprocedurein, CStringGetDatum(configuration.start_proc)));
      }
    }
  }
  PG_CATCH();
  {
    ErrorData *edata;

    // Switch out of the error memory context and back into the execution
    // context to get the error details
    MemoryContextSwitchTo(memory_context);

    edata = CopyErrorData();
    elog(WARNING, "failed to find pljs function %s: ", edata->message);
    FlushErrorState();
    FreeErrorData(edata);

    return;
  }
  PG_END_TRY();

  if (OidIsValid(funcoid)) {
    run.func = pljs_find_js_function(funcoid, ctx);
  }

  if (JS_IsUndefined(run.func)) {
    elog(DEBUG3, "javascript function is not found for \"%s\"",
         configuration.start_proc);
    return;
  }

  /*
   * The start_proc runs with storage of its own, as a DO block does, with no
   * set to return and no window.  A context is created on the first call a
   * user makes, which can be a call made from inside another --
   * pljs.execute() after SET ROLE -- and the start_proc saw that call's
   * storage: its pljs.return_next() added rows to the other call's set.
   */
  pljs_run_with_storage(ctx, NULL, NULL, true, run_start_proc, &run);
}

/* What pljs_run_with_storage() runs for pljs_hook_call(). */
typedef struct pljs_hook_call_run {
  JSContext *ctx;
  JSValueConst func;
  int argc;
  JSValueConst *argv;
  MemoryContext caller_context;
  JSValue *result;
  char **error;
  bool ok;
} pljs_hook_call_run;

/**
 * @brief Calls the hook's function; see pljs_hook_call().
 *
 * @param arg #pljs_hook_call_run - the call, and where its result goes
 */
static void run_hook_call(void *arg) {
  pljs_hook_call_run *run = (pljs_hook_call_run *)arg;
  JSValue ret =
      JS_Call(run->ctx, run->func, JS_UNDEFINED, run->argc, run->argv);

  if (JS_IsException(ret)) {
    run->ok = false;

    /*
     * Extracted while the SPI connection is open, as call_function() does, and
     * into the caller's context, which outlives SPI_finish().
     */
    if (run->error != NULL) {
      MemoryContext old_context = MemoryContextSwitchTo(run->caller_context);

      *run->error = pljs_dump_error(run->ctx);
      MemoryContextSwitchTo(old_context);
    } else {
      JS_FreeValue(run->ctx, JS_GetException(run->ctx));
    }
  } else if (run->result != NULL) {
    *run->result = ret;
    return;
  }

  JS_FreeValue(run->ctx, ret);
}

/**
 * @brief Calls a JavaScript function from a PostgreSQL hook.
 *
 * A hook runs outside of any pljs call, so the JavaScript it calls gets what a
 * call would have given it: storage of its own, and a cache for converting
 * types, without which pljs.execute() could not convert its parameters or its
 * results.  The cache lasts for this call only.
 *
 * @param ctx #JSContext - the context the function belongs to
 * @param func #JSValueConst - the function
 * @param argc @c int - how many arguments there are
 * @param argv #JSValueConst* - the arguments
 * @param own_spi @c bool - whether to connect to SPI for the call
 * @param result #JSValue* - set to what the function returned, which the
 * caller frees, or NULL to discard it; left alone when the function throws
 * @param error @c char** - set to the error when the function throws, or NULL
 * to discard it
 * @returns @c bool - false when the function threw
 */
bool pljs_hook_call(JSContext *ctx, JSValueConst func, int argc,
                    JSValueConst *argv, bool own_spi, JSValue *result,
                    char **error) {
  pljs_hook_call_run run = {.ctx = ctx,
                            .func = func,
                            .argc = argc,
                            .argv = argv,
                            .caller_context = CurrentMemoryContext,
                            .result = result,
                            .error = error,
                            .ok = true};
  MemoryContext type_io_context = AllocSetContextCreate(
      CurrentMemoryContext, "PLJS hook call", ALLOCSET_SMALL_SIZES);
  FmgrInfo flinfo;
  pljs_type_io_cache *types;

  memset(&flinfo, 0, sizeof(flinfo));
  flinfo.fn_oid = InvalidOid;
  flinfo.fn_mcxt = type_io_context;

  pljs_encoding_init();
  types = pljs_type_io_enter(&flinfo);

  PG_TRY();
  {
    pljs_run_with_storage(ctx, NULL, NULL, own_spi, run_hook_call, &run);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(types);
    MemoryContextDelete(type_io_context);
  }
  PG_END_TRY();

  return run.ok;
}

/**
 * @brief Creates the running user's JSContext, runs pljs.start_proc in it,
 * and caches it.
 *
 * A start_proc that raises -- one that throws, or times out, whether when it
 * is called or in code at the top level of its source -- leaves the context
 * uncached, and it is freed rather than lost: a function that failed because
 * of its user's start_proc created a context on every call, and kept none.
 *
 * @returns #JSContext - the new context
 */
JSContext *pljs_create_context(Oid user_id, Oid owner_id) {
  JSContext *ctx = JS_NewContext(rt);
  JSContext *prev_compiling_ctx = current_compiling_ctx;

  if (ctx == NULL) {
    elog(ERROR, "could not create a JavaScript context");
  }

  current_compiling_ctx = ctx;

  PG_TRY();
  {
    // Set up the namespace, globals and functions available inside the
    // context.
    pljs_setup_namespace(ctx);

    // Check to see if there is a start_proc, if there is, attempt to apply
    // it.
    if (configuration.start_proc != NULL &&
        strlen(configuration.start_proc) != 0) {
      setup_start_proc(ctx);
    }

    /*
     * Save the context in the cache for this (user_id, owner_id).  Inside the
     * PG_TRY: a start_proc that made a nested call as the same user/owner
     * cached a context of its own, and adding this one raised, and lost it.
     */
    pljs_cache_context_add(user_id, owner_id, ctx);
  }
  PG_CATCH();
  {
    current_compiling_ctx = prev_compiling_ctx;
    JS_FreeContext(ctx);
    PG_RE_THROW();
  }
  PG_END_TRY();

  current_compiling_ctx = prev_compiling_ctx;

  return ctx;
}

/**
 * @brief Whether an argument of a mode is an input argument, and so one of
 * the call's.
 *
 * @param argmode @c char - the argument's mode
 * @returns @c bool
 */
static bool pljs_argmode_is_input(char argmode) {
  return argmode == PROARGMODE_IN || argmode == PROARGMODE_INOUT ||
         argmode == PROARGMODE_VARIADIC;
}

/**
 * @brief Resolves a declared argument type against the call being made.
 *
 * Polymorphic types and `"any"` only name a concrete type at the call site.
 * `IsPolymorphicType()` covers the anyelement family but excludes `"any"`.
 *
 * @param fcinfo #FunctionCallInfo - the call in progress, may be NULL
 * @param argtype #Oid - the argument's declared type
 * @param argno @c int - which input argument: its place in the call, which
 * has no OUT arguments
 * @returns #Oid of the type the datum actually has
 */
static Oid pljs_resolve_argtype(FunctionCallInfo fcinfo, Oid argtype,
                                int argno) {
  if (fcinfo == NULL || !(IsPolymorphicType(argtype) || argtype == ANYOID)) {
    return argtype;
  }

  Oid resolved = get_fn_expr_argtype(fcinfo->flinfo, argno);

  return OidIsValid(resolved) ? resolved : argtype;
}

/**
 * @brief Converts all function call arguments from postgres to Javascript.
 *
 * Allocates and creates an array of arguments as Javascript values.
 *
 * @param fcinfo #FunctionCallInfo
 * @param proctuple #HeapTuple
 * @param context #pljs_context
 * @param argc @c int* - set to the number of values in the array, all of
 * which the caller owns
 * @returns an array of #JSValueConst values of the function arguments
 */
static JSValueConst *convert_arguments_to_javascript(FunctionCallInfo fcinfo,
                                                     HeapTuple proctuple,
                                                     pljs_context *context,
                                                     int *argc) {
  char **arguments;
  Oid *argtypes = NULL;
  char *argmodes;
  int nargs;

  nargs = get_func_arg_info(proctuple, &argtypes, &arguments, &argmodes);
  *argc = nargs;

  JSValueConst *argv = (JSValueConst *)palloc(sizeof(JSValueConst) * nargs);
  int inargs = 0;

  WindowObject window_obj = PG_WINDOW_OBJECT();

  /*
   * Every element is `undefined` until it is converted, so that when one of
   * them raises, the ones converted before it can be released: the caller
   * only frees the arguments once this has returned them, and the values
   * converted so far stayed in the runtime -- a 1MB text argument for every
   * call whose next argument was a multidimensional array.
   */
  for (int i = 0; i < nargs; i++) {
    argv[i] = JS_UNDEFINED;
  }

  PG_TRY();
  {
    /*
     * The input arguments, by their place in the call: a window's, or fcinfo's,
     * which have no OUT arguments.  They were read, and their polymorphic
     * types resolved, by their place among all of the arguments, and an OUT
     * argument before one moved it: f(OUT r int, a anyelement, b anyarray)
     * took a for an int4[], and read the int 5 it was passed as an array's
     * address, and a window function read past the end of its arguments.
     */
    bool is_window = WindowObjectIsValid(window_obj);

    for (int i = 0; i < nargs; i++) {
      Datum arg;
      bool is_null;

      if (!pljs_argmode_is_input(argmodes ? argmodes[i] : PROARGMODE_IN)) {
        continue;
      }

      if (is_window) {
        arg = WinGetFuncArgCurrent(window_obj, inargs, &is_null);
      } else {
        arg = fcinfo->args[inargs].value;
        is_null = fcinfo->args[inargs].isnull;
      }

      // Window functions: expand_composite=false (skip composite expansion),
      // regular functions: expand_composite=true (expand composite types)
      argv[inargs] = pljs_datum_to_jsvalue(
          pljs_resolve_argtype(fcinfo, argtypes[i], inargs), arg, is_null,
          !is_window, context->ctx);

      inargs++;
    }
  }
  PG_CATCH();
  {
    for (int i = 0; i < nargs; i++) {
      JS_FreeValue(context->ctx, argv[i]);
    }

    PG_RE_THROW();
  }
  PG_END_TRY();

  return argv;
}

/**
 * @brief Retrieves the #pljs_storage of the pljs call running now.
 *
 * The storage holds what the builtins need from the call that is running --
 * its FunctionCallInfo, the set it returns, its window -- and every entry
 * point that runs JavaScript installs its own and restores the previous one
 * however it leaves.
 *
 * It was kept as the opaque of the global `pljs` object, which JavaScript can
 * replace or delete: after `globalThis.pljs = undefined` the lookup returned
 * NULL, and the next call dereferenced it and crashed the backend, for any
 * user of the trusted language.  A function compiled in another user's
 * JSContext -- reached through pljs.find_function() after SET ROLE -- saw
 * that context's storage rather than the running call's.
 *
 * @returns #pljs_storage, or NULL outside of a pljs call
 */
pljs_storage *pljs_current_storage(void) { return current_storage; }

/**
 * @brief Fills in a #pljs_storage for a call.
 *
 * @param storage #pljs_storage - the storage to fill
 * @param function #pljs_func - the function being called, or NULL for a DO
 * block or a start_proc
 * @param fcinfo #FunctionCalInfo - the call, or NULL for a start_proc
 */
static void setup_storage(pljs_storage *storage, JSContext *ctx,
                          pljs_func *function, FunctionCallInfo fcinfo) {
  WindowObject window_object = fcinfo != NULL ? PG_WINDOW_OBJECT() : NULL;

  memset(storage, 0, sizeof(pljs_storage));

  storage->function = function;
  storage->execution_memory_context = CurrentMemoryContext;
  storage->fcinfo = fcinfo;
  storage->ctx = ctx;
  storage->previous = current_storage;

  /* fcinfo->context is a TriggerData or CallContext for other calls. */
  if (WindowObjectIsValid(window_object)) {
    storage->window_object = window_object;
  }
}

/**
 * @brief Runs JavaScript with storage of its own.
 *
 * What every entry point into JavaScript does around it: a call, a DO block,
 * a pljs.start_proc, and code at the top level of a function's source, which
 * runs as it is compiled.  The storage is installed; the error the call has to
 * end with is raised, should the JavaScript run to its end all the same,
 * since C code can catch the exception that was to end it (see
 * pljs_throw_fatal_error()); and the storage that was installed before is
 * restored however it ends.  Each entry point had a copy of these steps, and
 * the copies had drifted apart.
 *
 * @param function #pljs_func - the function being called, or NULL
 * @param fcinfo #FunctionCallInfo - the call, or NULL
 * @param run - runs the JavaScript
 * @param arg - @p run's argument
 */
static void pljs_run_with_storage(JSContext *ctx, pljs_func *function,
                                  FunctionCallInfo fcinfo, bool own_spi,
                                  void (*run)(void *), void *arg) {
  pljs_storage storage;
  pljs_storage *previous_storage = current_storage;
  bool prev_pnp = pljs_preserve_numeric_precision;
  bool prev_putb = pljs_pass_user_types_as_bytes;
  volatile bool connected = false;

  setup_storage(&storage, ctx, function, fcinfo);
  current_storage = &storage;
  if (function != NULL) {
    pljs_preserve_numeric_precision = function->preserve_numeric_precision;
    pljs_pass_user_types_as_bytes = function->pass_user_types_as_bytes;
  }

  PG_TRY();
  {
    /*
     * Code with no call of its own -- a function's top-level code, a
     * start_proc -- gets a connection to SPI of its own, as a call's does, and
     * its stack is measured from here; see call_function().  It ran on
     * whatever connection was on top of the stack, a PL/pgSQL loop's
     * included, where pljs.execute() failed with "improper call to
     * spi_printtup", and against a stack anchored by some other call.  Atomic:
     * it cannot commit.
     */
    if (own_spi) {
      /*
       * Re-anchoring gives QuickJS its whole budget again from here, so the C
       * stack below has to be checked first: nothing else on the way checks
       * it when pljs.find_function() compiles a function from inside
       * JavaScript, and recursion through it re-anchored at every level until
       * the backend crashed.
       */
      check_stack_depth();

      if (SPI_connect() != SPI_OK_CONNECT) {
        elog(ERROR, "could not connect to spi manager");
      }

      connected = true;
      JS_UpdateStackTop(rt);
    }

    run(arg);

    if (connected) {
      connected = false;
      SPI_finish();
    }

    if (storage.fatal_error != NULL) {
      ReThrowError(storage.fatal_error);
    }
  }
  PG_FINALLY();
  {
    /*
     * The connection is finished on the way out with an error too.  Only
     * rolling back a subtransaction begun around this finished it otherwise,
     * and where none can be begun -- pljs.find_function() compiling a
     * function in parallel mode, before PostgreSQL 17 -- JavaScript that
     * caught the error went on with it on top of the SPI stack: the call's
     * own SPI_finish() finished it in place of the call's connection, and
     * the transaction ended with "transaction left non-empty SPI stack".
     * The error is being handled in ErrorContext, which is gone back to.
     */
    if (connected) {
      MemoryContext error_context = CurrentMemoryContext;

      SPI_finish();
      MemoryContextSwitchTo(error_context);
    }

    /*
     * The key of a set's column, kept for the call; see
     * pljs_single_column_value().  Read through current_storage, which is
     * this call's still, and not a local the PG_TRY wrote.
     */
    if (current_storage->return_state != NULL &&
        current_storage->return_state->column_atom != JS_ATOM_NULL) {
      JS_FreeAtomRT(rt, current_storage->return_state->column_atom);
      current_storage->return_state->column_atom = JS_ATOM_NULL;
    }

    current_storage = previous_storage;
    pljs_preserve_numeric_precision = prev_pnp;
    pljs_pass_user_types_as_bytes = prev_putb;
  }
  PG_END_TRY();

  pljs_cache_evict_excess(configuration.max_cached_contexts);
}

/**
 * @brief Retrieves or creates the cached #JSContext for the given
 * (user_id, owner_id) pair.
 */
static JSContext *pljs_get_context(Oid user_id, Oid owner_id) {
  pljs_context_cache_value *entry = pljs_cache_context_find(user_id, owner_id);
  return entry ? entry->ctx : pljs_create_context(user_id, owner_id);
}

/**
 * @brief Retrieves or creates the cached #JSContext for the current user
 * (when there is no separate function owner, such as a DO block).
 */
static JSContext *pljs_get_user_context(void) {
  Oid user_id = GetUserId();
  return pljs_get_context(user_id, user_id);
}

/**
 * @brief Checks whether a language OID is `pljs` or a custom language whose
 * handler chain resolves to `pljs`.
 */
static bool pljs_is_js_language(Oid prolang, bool *too_deep) {
  Oid current_lang = prolang;

  if (too_deep != NULL) {
    *too_deep = false;
  }

  for (int depth = 0; depth < PLJS_MAX_LANG_HANDLER_DEPTH; depth++) {
    CHECK_FOR_INTERRUPTS();

    if (!OidIsValid(current_lang)) {
      return false;
    }

    HeapTuple langtuple =
        SearchSysCache(LANGOID, ObjectIdGetDatum(current_lang), 0, 0, 0);
    if (!HeapTupleIsValid(langtuple)) {
      return false;
    }

    Form_pg_language lang_entry = (Form_pg_language)GETSTRUCT(langtuple);
    bool is_pljs = (strcmp(NameStr(lang_entry->lanname), "pljs") == 0);
    Oid lanplcallfoid = lang_entry->lanplcallfoid;
    ReleaseSysCache(langtuple);

    if (is_pljs) {
      return true;
    }

    if (!OidIsValid(lanplcallfoid)) {
      return false;
    }

    HeapTuple proctuple =
        SearchSysCache(PROCOID, ObjectIdGetDatum(lanplcallfoid), 0, 0, 0);
    if (!HeapTupleIsValid(proctuple)) {
      return false;
    }

    Form_pg_proc proc_entry = (Form_pg_proc)GETSTRUCT(proctuple);
    current_lang = proc_entry->prolang;
    ReleaseSysCache(proctuple);
  }

  if (too_deep != NULL) {
    *too_deep = true;
  }

  return false;
}

/**
 * @brief Records the chain of language handler functions (`fn_oid`, `fn_xmin`,
 * `fn_tid`) that transpile `func`, so downstream cached functions can be
 * invalidated automatically when any handler in the chain is replaced.
 */
static void pljs_record_language_handlers(Oid first_handler_oid,
                                          pljs_func *func) {
  Oid current_handler = first_handler_oid;
  func->nhandlers = 0;

  for (int depth = 0; depth < PLJS_MAX_LANG_HANDLER_DEPTH; depth++) {
    CHECK_FOR_INTERRUPTS();

    if (!OidIsValid(current_handler)) {
      break;
    }

    HeapTuple proctuple =
        SearchSysCache(PROCOID, ObjectIdGetDatum(current_handler), 0, 0, 0);
    if (!HeapTupleIsValid(proctuple)) {
      break;
    }

    func->handlers[func->nhandlers].fn_oid = current_handler;
    func->handlers[func->nhandlers].fn_xmin =
        HeapTupleHeaderGetRawXmin(proctuple->t_data);
    func->handlers[func->nhandlers].fn_tid = proctuple->t_self;
    func->nhandlers++;

    Form_pg_proc proc_entry = (Form_pg_proc)GETSTRUCT(proctuple);
    Oid next_lang = proc_entry->prolang;
    ReleaseSysCache(proctuple);

    if (!OidIsValid(next_lang)) {
      break;
    }

    HeapTuple langtuple =
        SearchSysCache(LANGOID, ObjectIdGetDatum(next_lang), 0, 0, 0);
    if (!HeapTupleIsValid(langtuple)) {
      break;
    }

    Form_pg_language lang_entry = (Form_pg_language)GETSTRUCT(langtuple);
    bool is_pljs = (strcmp(NameStr(lang_entry->lanname), "pljs") == 0);
    current_handler = lang_entry->lanplcallfoid;
    ReleaseSysCache(langtuple);

    if (is_pljs) {
      break;
    }
  }
}

typedef struct pljs_transpile_run {
  JSContext *ctx;
  JSValue transpiler_func;
  JSValue argv[2];
  JSValue result;
} pljs_transpile_run;

static void transpile_run(void *arg) {
  pljs_transpile_run *run = (pljs_transpile_run *)arg;

  JS_SetInterruptHandler(JS_GetRuntime(run->ctx), interrupt_handler, NULL);
  run->result =
      JS_Call(run->ctx, run->transpiler_func, JS_UNDEFINED, 2, run->argv);
}

/**
 * @brief If the function's language is a custom language handled by a JS
 * function, transpile `context->function->prosrc` using the language handler.
 */
static bool pljs_transpile_if_needed(pljs_context *context, Oid lang_oid) {
  check_stack_depth();
  CHECK_FOR_INTERRUPTS();

  Oid prolang = lang_oid;

  if (!OidIsValid(prolang) && OidIsValid(context->function->fn_oid)) {
    HeapTuple proctuple = SearchSysCache(
        PROCOID, ObjectIdGetDatum(context->function->fn_oid), 0, 0, 0);
    if (!HeapTupleIsValid(proctuple)) {
      elog(ERROR, "cache lookup failed for function %u",
           context->function->fn_oid);
    }
    Form_pg_proc proc_struct = (Form_pg_proc)GETSTRUCT(proctuple);
    prolang = proc_struct->prolang;
    ReleaseSysCache(proctuple);
  }

  if (!OidIsValid(prolang)) {
    return true;
  }

  HeapTuple langtuple =
      SearchSysCache(LANGOID, ObjectIdGetDatum(prolang), 0, 0, 0);
  if (!HeapTupleIsValid(langtuple)) {
    elog(ERROR, "cache lookup failed for language %u", prolang);
  }

  Form_pg_language lang_struct = (Form_pg_language)GETSTRUCT(langtuple);
  bool lang_is_pljs = (strcmp(NameStr(lang_struct->lanname), "pljs") == 0);
  Oid lanplcallfoid = lang_struct->lanplcallfoid;
  char lanname[NAMEDATALEN];
  memcpy(lanname, NameStr(lang_struct->lanname), NAMEDATALEN);
  ReleaseSysCache(langtuple);

  if (lang_is_pljs) {
    return true;
  }

  ereport(DEBUG1,
          (errmsg("pl/<any>: prolang %u, lanname [%s], lang_is_pljs: %d",
                  prolang, lanname, lang_is_pljs)));

  bool all_handlers_superuser = true;
  bool is_wasm_lang = false;
  {
    Oid cur_lang = prolang;
    for (int depth = 0;
         depth < PLJS_MAX_LANG_HANDLER_DEPTH && OidIsValid(cur_lang);
         depth++) {
      HeapTuple lt =
          SearchSysCache(LANGOID, ObjectIdGetDatum(cur_lang), 0, 0, 0);
      if (!HeapTupleIsValid(lt)) {
        break;
      }
      Form_pg_language ls = (Form_pg_language)GETSTRUCT(lt);
      if (strcmp(NameStr(ls->lanname), "pljs") == 0) {
        ReleaseSysCache(lt);
        break;
      }
      if (strcmp(NameStr(ls->lanname), "pl/v8-wasm") == 0 ||
          strcmp(NameStr(ls->lanname), "pl/js-wasm") == 0) {
        is_wasm_lang = true;
      }
      if (!superuser_arg(ls->lanowner)) {
        all_handlers_superuser = false;
      }
      Oid h_oid = ls->lanplcallfoid;
      ReleaseSysCache(lt);
      if (!OidIsValid(h_oid)) {
        break;
      }
      HeapTuple pt = SearchSysCache(PROCOID, ObjectIdGetDatum(h_oid), 0, 0, 0);
      if (!HeapTupleIsValid(pt)) {
        break;
      }
      Form_pg_proc ps = (Form_pg_proc)GETSTRUCT(pt);
      if (!superuser_arg(ps->proowner)) {
        all_handlers_superuser = false;
      }
      cur_lang = ps->prolang;
      ReleaseSysCache(pt);
    }
  }

  if (OidIsValid(context->function->fn_oid)) {
    pljs_record_language_handlers(lanplcallfoid, context->function);
  }

  JSValue transpiler_func = pljs_find_js_function(lanplcallfoid, context->ctx);
  if (JS_IsUndefined(transpiler_func)) {
    /*
     * A handler written in a language that is itself handled by a chain of
     * more than PLJS_MAX_LANG_HANDLER_DEPTH handlers is not found either;
     * say so, rather than blaming a handler that exists.
     */
    HeapTuple handler_tuple =
        SearchSysCache(PROCOID, ObjectIdGetDatum(lanplcallfoid), 0, 0, 0);
    if (HeapTupleIsValid(handler_tuple)) {
      Oid handler_lang = ((Form_pg_proc)GETSTRUCT(handler_tuple))->prolang;
      bool too_deep = false;

      ReleaseSysCache(handler_tuple);
      if (!pljs_is_js_language(handler_lang, &too_deep) && too_deep) {
        ereport(ERROR,
                (errcode(ERRCODE_PROGRAM_LIMIT_EXCEEDED),
                 errmsg("language handler chain is deeper than %d levels",
                        PLJS_MAX_LANG_HANDLER_DEPTH)));
      }
    }

    elog(ERROR, "javascript language handler function %u is not found",
         lanplcallfoid);
  }

  JSValue argv0 = JS_NewStringLen(context->ctx, context->function->prosrc,
                                  strlen(context->function->prosrc));
  if (JS_IsException(argv0)) {
    pljs_js_error_info errinfo;
    dump_error_ex(context->ctx, &errinfo);
    JS_FreeValue(context->ctx, argv0);
    JS_FreeValue(context->ctx, transpiler_func);
    pljs_ereport_js_error_info(&errinfo, "language handler execution error");
  }

  JSValue meta = JS_NewObject(context->ctx);
  if (OidIsValid(context->function->fn_oid)) {
    JS_SetPropertyStr(context->ctx, meta, "fn_oid",
                      JS_NewUint32(context->ctx, context->function->fn_oid));
    JS_SetPropertyStr(context->ctx, meta, "proname",
                      JS_NewString(context->ctx, context->function->proname));
    JS_SetPropertyStr(context->ctx, meta, "rettype_oid",
                      JS_NewUint32(context->ctx, context->function->rettype));

    char ret_cat = '\0';
    bool ret_pref = false;
    int16 ret_typlen = 0;
    if (OidIsValid(context->function->rettype)) {
      get_type_category_preferred(context->function->rettype, &ret_cat,
                                  &ret_pref);
      ret_typlen = get_typlen(context->function->rettype);
    }
    char ret_cat_str[2] = {ret_cat, '\0'};
    JS_SetPropertyStr(context->ctx, meta, "rettype_category",
                      JS_NewString(context->ctx, ret_cat_str));
    int32 ret_internal_len = (ret_typlen > (int16)VARHDRSZ)
                                 ? (int32)(ret_typlen - VARHDRSZ)
                                 : (int32)ret_typlen;
    JS_SetPropertyStr(context->ctx, meta, "rettype_len",
                      JS_NewInt32(context->ctx, ret_internal_len));

    JSValue arg_oids = JS_NewArray(context->ctx);
    JSValue arg_cats = JS_NewArray(context->ctx);
    JSValue arg_lens = JS_NewArray(context->ctx);
    for (int a = 0; a < context->function->inargs; a++) {
      Oid atype = context->function->argtypes[a];
      JS_SetPropertyUint32(context->ctx, arg_oids, (uint32_t)a,
                           JS_NewUint32(context->ctx, atype));
      char acat = '\0';
      bool apref = false;
      int16 alen_raw = 0;
      if (OidIsValid(atype)) {
        get_type_category_preferred(atype, &acat, &apref);
        alen_raw = get_typlen(atype);
      }
      char acat_str[2] = {acat, '\0'};
      JS_SetPropertyUint32(context->ctx, arg_cats, (uint32_t)a,
                           JS_NewString(context->ctx, acat_str));
      int32 alen = (alen_raw > (int16)VARHDRSZ) ? (int32)(alen_raw - VARHDRSZ)
                                                : (int32)alen_raw;
      JS_SetPropertyUint32(context->ctx, arg_lens, (uint32_t)a,
                           JS_NewInt32(context->ctx, alen));
    }
    JS_SetPropertyStr(context->ctx, meta, "argtype_oids", arg_oids);
    JS_SetPropertyStr(context->ctx, meta, "argtype_categories", arg_cats);
    JS_SetPropertyStr(context->ctx, meta, "argtype_lens", arg_lens);
  } else {
    JS_SetPropertyStr(context->ctx, meta, "inline", JS_NewBool(context->ctx, 1));
  }

  pljs_func handler_func = {0};
  handler_func.fn_oid = lanplcallfoid;
  handler_func.user_id = GetUserId();
  handler_func.owner_id =
      context->function ? context->function->owner_id : GetUserId();

  pljs_transpile_run run = {
      .ctx = context->ctx,
      .transpiler_func = transpiler_func,
      .argv = {argv0, meta},
      .result = JS_UNDEFINED,
  };

  PG_TRY();
  {
    pljs_run_with_storage(context->ctx, &handler_func, NULL, true,
                          transpile_run, &run);
  }
  PG_CATCH();
  {
    JS_FreeValue(context->ctx, run.result);
    JS_FreeValue(context->ctx, argv0);
    JS_FreeValue(context->ctx, meta);
    JS_FreeValue(context->ctx, transpiler_func);
    PG_RE_THROW();
  }
  PG_END_TRY();

  JSValue pnp_val =
      JS_GetPropertyStr(context->ctx, meta, "preserve_numeric_precision");
  if (JS_IsBool(pnp_val) && JS_ToBool(context->ctx, pnp_val) > 0) {
    context->function->preserve_numeric_precision = true;
  }
  JS_FreeValue(context->ctx, pnp_val);

  JSValue putb_val =
      JS_GetPropertyStr(context->ctx, meta, "pass_user_types_as_bytes");
  bool explicit_pass_bytes =
      (JS_IsBool(putb_val) && JS_ToBool(context->ctx, putb_val) > 0);
  JS_FreeValue(context->ctx, putb_val);

  bool owner_is_superuser =
      all_handlers_superuser &&
      (!OidIsValid(context->function->owner_id) ||
       superuser_arg(context->function->owner_id));
  if (explicit_pass_bytes && !owner_is_superuser) {
    JS_FreeValue(context->ctx, run.result);
    JS_FreeValue(context->ctx, argv0);
    JS_FreeValue(context->ctx, meta);
    JS_FreeValue(context->ctx, transpiler_func);
    ereport(ERROR,
            (errcode(ERRCODE_INSUFFICIENT_PRIVILEGE),
             errmsg("must be superuser to enable pass_user_types_as_bytes")));
  }
  context->function->pass_user_types_as_bytes =
      (is_wasm_lang || explicit_pass_bytes) && owner_is_superuser;

  JS_FreeValue(context->ctx, argv0);
  JS_FreeValue(context->ctx, meta);
  JS_FreeValue(context->ctx, transpiler_func);

  if (JS_IsException(run.result)) {
    pljs_js_error_info errinfo;
    dump_error_ex(context->ctx, &errinfo);

    JS_FreeValue(context->ctx, run.result);

    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "language handler execution error");
  }

  if (JS_IsNull(run.result) || JS_IsUndefined(run.result)) {
    JS_FreeValue(context->ctx, run.result);
    elog(ERROR, "language handler returned null or undefined source code");
  }

  if (!JS_IsString(run.result)) {
    JS_FreeValue(context->ctx, run.result);
    ereport(ERROR,
            (errcode(ERRCODE_DATATYPE_MISMATCH),
             errmsg("language handler function %u did not return a string",
                    lanplcallfoid)));
  }

  size_t transpiled_len = 0;
  const char *transpiled =
      JS_ToCStringLen(context->ctx, &transpiled_len, run.result);
  if (transpiled == NULL) {
    pljs_js_error_info errinfo;
    dump_error_ex(context->ctx, &errinfo);
    JS_FreeValue(context->ctx, run.result);
    pljs_ereport_js_error_info(&errinfo, "language handler execution error");
  }

  char *volatile new_prosrc = NULL;
  PG_TRY();
  {
    new_prosrc = pstrdup(transpiled);
  }
  PG_FINALLY();
  {
    JS_FreeCString(context->ctx, transpiled);
    JS_FreeValue(context->ctx, run.result);
  }
  PG_END_TRY();

  ereport(DEBUG1, (errmsg("pl/<any>: transpiled [%s] to [%s]",
                          context->function->prosrc, new_prosrc)));

  context->function->prosrc = new_prosrc;
  return true;
}

/**
 * @brief Call Javascript from PostgreSQL.
 *
 * Calls Javascript in some form from PostgreSQL, returning the result on
 * success, or throwing an error on exception.  Calls can be of types
 * `function`, `procedure`, `do`, or `trigger`, and are dispatched from this
 * entry point.
 *
 * @param PG_FUNCTION_ARGS Pointer to struct FunctionCallInfoBaseData
 * @returns #Datum of the result
 */
Datum pljs_call_handler(PG_FUNCTION_ARGS) {
  pljs_type_io_cache *types;
  Datum retval;

  pljs_reset_all_stamped_procs();
  pljs_encoding_init();
  types = pljs_type_io_enter(fcinfo->flinfo);

  PG_TRY();
  {
    retval = dispatch_call(fcinfo);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(types);
  }
  PG_END_TRY();

  return retval;
}

/**
 * @brief Calls a pljs function, procedure or trigger; see pljs_call_handler().
 *
 * @param fcinfo #FunctionCallInfo - the call
 * @returns #Datum of the result
 */
/* What pljs_run_with_storage() runs for dispatch_call(). */
typedef struct pljs_dispatch_run {
  FunctionCallInfo fcinfo;
  pljs_context *context;
  JSValueConst *argv;
  bool is_trigger;
  Datum retval;
} pljs_dispatch_run;

/**
 * @brief Calls a function, procedure or trigger; see dispatch_call().
 *
 * @param arg #pljs_dispatch_run - the call, whose retval is set
 */
static void dispatch_run(void *arg) {
  pljs_dispatch_run *run = (pljs_dispatch_run *)arg;

  if (run->is_trigger) {
    run->retval = call_trigger(run->fcinfo, run->context);
  } else if (run->context->function->is_srf) {
    run->retval = call_srf_function(run->fcinfo, run->context, run->argv);
  } else {
    run->retval = call_function(run->fcinfo, run->context, run->argv);
  }
}

static Datum dispatch_call(FunctionCallInfo fcinfo) {
  Oid fn_oid = fcinfo->flinfo->fn_oid;
  HeapTuple proctuple;
  JSContext *ctx;
  /* Read in the PG_FINALLY below. */
  JSValueConst *volatile argv = NULL;
  volatile int argc = 0;

  bool is_trigger = CALLED_AS_TRIGGER(fcinfo);
  pljs_context context = {0};

  proctuple = SearchSysCache(PROCOID, ObjectIdGetDatum(fn_oid), 0, 0, 0);

  if (!HeapTupleIsValid(proctuple)) {
    ereport(ERROR, errcode(ERRCODE_INTERNAL_ERROR),
            errmsg("cache lookup failed for function %u", fn_oid));
  }

  if (!is_trigger && fcinfo->nargs == 1 && !PG_ARGISNULL(0)) {
    Form_pg_proc procStruct = (Form_pg_proc)GETSTRUCT(proctuple);
    if (procStruct->pronargs == 1 &&
        procStruct->proargtypes.values[0] == INTERNALOID &&
        procStruct->prorettype == VOIDOID) {
      Node *arg0 = (Node *)DatumGetPointer(PG_GETARG_DATUM(0));
      if (arg0 != NULL && IsA(arg0, InlineCodeBlock)) {
        ReleaseSysCache(proctuple);
        run_inline(fcinfo);
        PG_RETURN_VOID();
      }
    }
  }

  Form_pg_proc procStruct_initial = (Form_pg_proc)GETSTRUCT(proctuple);
  Oid user_id = GetUserId();
  Oid owner_id = procStruct_initial->proowner;
  JSContext *prev_compiling_ctx = current_compiling_ctx;

  // First search for a cached copy of the context.
  pljs_function_cache_value *function_entry =
      pljs_cache_function_find(user_id, owner_id, fn_oid, proctuple);

  if (function_entry) {
    // Make a copy of the function entry to the pljs context.
    pljs_function_cache_to_context(&context, function_entry);
    current_compiling_ctx = context.ctx;
  } else {
    // Set up a copy of all of the function data and release the syscache pin
    // before entering JavaScript (start_proc or language handler transpiler).
    setup_function(fcinfo, proctuple, &context);
    ReleaseSysCache(proctuple);
    proctuple = NULL;

    ctx = pljs_get_context(user_id, owner_id);
    context.ctx = ctx;
    current_compiling_ctx = ctx;

    PG_TRY();
    {
      // Compile the function.
      context.js_function = pljs_compile_function(&context, is_trigger);

      /*
       * The source evaluates to the function it declares, unless its top-level
       * code replaced that: `} f = undefined; function z() {`.  That returned
       * void, a zero Datum not marked NULL, whatever the function's type, and
       * the caller took it for a pointer to text and crashed the backend.
       */
      if (!JS_IsFunction(context.ctx, context.js_function)) {
        JS_FreeValue(context.ctx, context.js_function);

        ereport(ERROR, (errcode(ERRCODE_INVALID_FUNCTION_DEFINITION),
                        errmsg("the source of function %s does not evaluate to "
                               "a function",
                               context.function->proname)));
      }

      // Create the cache entry for the function.
      pljs_cache_function_add(&context);
    }
    PG_CATCH();
    {
      current_compiling_ctx = prev_compiling_ctx;
      PG_RE_THROW();
    }
    PG_END_TRY();
  }

  /*
   * NB: `proctuple` must stay pinned until we have finished reading from it,
   * but it MUST be released before we enter JavaScript, because a PROCEDURE
   * can run COMMIT/ROLLBACK internally and it is illegal to hold a syscache
   * pin across a transaction boundary (it trips "resource was not closed").
   *
   * The original code released the pin up front, before either branch, which
   * was a use-after-free: the trigger branch still read GETSTRUCT(proctuple)
   * and the function branch still passed the tuple to
   * convert_arguments_to_javascript() -> get_func_arg_info().  That only bit
   * once the entry was actually evicted (cache pressure / concurrent DDL in a
   * long-running backend).  Release it at the last safe point instead: right
   * after the final read, before any JS is executed.
   */
  bool prev_pnp_arg = pljs_preserve_numeric_precision;
  bool prev_putb_arg = pljs_pass_user_types_as_bytes;
  pljs_preserve_numeric_precision = context.function->preserve_numeric_precision;
  pljs_pass_user_types_as_bytes = context.function->pass_user_types_as_bytes;

  PG_TRY();
  {
    if (is_trigger) {
      // Call in the context of a trigger.
      if (proctuple != NULL) {
        Form_pg_proc procStruct = (Form_pg_proc)GETSTRUCT(proctuple);
        context.function->rettype = procStruct->prorettype;
        ReleaseSysCache(proctuple);
      }
    } else {
      // Call as a function.
      int nargs;

      if (proctuple == NULL) {
        proctuple = SearchSysCache(PROCOID, ObjectIdGetDatum(fn_oid), 0, 0, 0);
        if (!HeapTupleIsValid(proctuple)) {
          ereport(ERROR, errcode(ERRCODE_INTERNAL_ERROR),
                  errmsg("cache lookup failed for function %u", fn_oid));
        }
      }

      argv =
          convert_arguments_to_javascript(fcinfo, proctuple, &context, &nargs);
      argc = nargs;
      ReleaseSysCache(proctuple);
    }
  }
  PG_FINALLY();
  {
    current_compiling_ctx = prev_compiling_ctx;
    pljs_preserve_numeric_precision = prev_pnp_arg;
    pljs_pass_user_types_as_bytes = prev_putb_arg;
  }
  PG_END_TRY();

  pljs_dispatch_run run = {.fcinfo = fcinfo,
                           .context = &context,
                           .argv = argv,
                           .is_trigger = is_trigger};

  /*
   * Retain a local reference to context.js_function across execution in case
   * the function cache entry is invalidated during a nested SPI call.
   */
  JS_DupValue(context.ctx, context.js_function);

  /*
   * The storage is restored even when the call raises; see
   * pljs_run_with_storage().
   *
   * A call that raised used to leave its own storage installed permanently --
   * pointing at this call's fcinfo, its return_state and its execution memory
   * context, all of which are gone once the error has unwound.  The next call
   * of *any* kind that reads pljs_current_storage() -- a trigger, a window
   * function, return_next() -- then dereferenced that stale pointer and
   * segfaulted the backend.
   *
   * This was latent until a conversion error became reachable from inside a
   * set-returning function: before that, returning an out-of-range integer
   * wrapped silently instead of raising, so nothing escaped this block.  A
   * failing SETOF call followed by any trigger reproduces it within a couple
   * of dozen iterations.
   *
   * The arguments are released here too.  JS_Call() takes references of its
   * own, so these were never freed at all, and every call leaked its
   * arguments into the runtime for the life of the backend -- 20MB over
   * 20,000 calls with a 1kB text argument, until pljs.memory_limit was
   * exhausted for good.
   */
  PG_TRY();
  {
    pljs_run_with_storage(context.ctx, context.function, fcinfo, false,
                          dispatch_run, &run);
  }
  PG_FINALLY();
  {
    for (int i = 0; i < argc; i++) {
      JS_FreeValue(context.ctx, argv[i]);
    }
    JS_FreeValue(context.ctx, context.js_function);
  }
  PG_END_TRY();

  return run.retval;
}

/**
 * @brief Execute an inline javascript call.
 *
 * Executes whatever is passed as a `DO` call in postgres, does
 * not accept any arguments to the call, nor allow for any returned
 * data.
 *
 * @returns #Datum containing `VOID`
 */
Datum pljs_inline_handler(PG_FUNCTION_ARGS) {
  pljs_type_io_cache *types;

  pljs_encoding_init();
  types = pljs_type_io_enter(fcinfo->flinfo);

  PG_TRY();
  {
    run_inline(fcinfo);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(types);
  }
  PG_END_TRY();

  PG_RETURN_VOID();
}

/**
 * @brief Runs a `DO` block; see pljs_inline_handler().
 *
 * @param fcinfo #FunctionCallInfo - the inline handler's call
 */
/* What pljs_run_with_storage() runs for run_inline(). */
typedef struct pljs_inline_run {
  const char *source;
  JSContext *ctx;
} pljs_inline_run;

/**
 * @brief Runs a DO block's code; see run_inline().
 *
 * @param arg #pljs_inline_run - the code and the context to run it in
 */
static void inline_run(void *arg) {
  pljs_inline_run *run = (pljs_inline_run *)arg;

  call_anonymous_function(run->source, run->ctx);
}

static void run_inline(FunctionCallInfo fcinfo) {
  InlineCodeBlock *code_block =
      (InlineCodeBlock *)DatumGetPointer(PG_GETARG_DATUM(0));
  char *sourcecode = pljs_server_to_utf8(code_block->source_text,
                                         strlen(code_block->source_text));

  bool nonatomic = fcinfo->context && IsA(fcinfo->context, CallContext) &&
                   !castNode(CallContext, fcinfo->context)->atomic;

  JSContext *ctx = pljs_get_user_context();

  pljs_func local_func = {0};
  local_func.fn_oid = InvalidOid;
  local_func.prosrc = sourcecode;
  local_func.user_id = GetUserId();
  local_func.owner_id = GetUserId();

  pljs_context local_context = {0};
  local_context.ctx = ctx;
  local_context.function = &local_func;

  if (!pljs_transpile_if_needed(&local_context, code_block->langOid)) {
    elog(ERROR, "failed to transpile function source code");
  }
  sourcecode = local_func.prosrc;

  if (SPI_connect_ext(nonatomic ? SPI_OPT_NONATOMIC : 0) != SPI_OK_CONNECT) {
    elog(ERROR, "could not connect to spi manager");
  }

  /*
   * A DO block has storage of its own, with no set to return and no window:
   * it used to see whatever the call further up the stack had installed, so
   * pljs.return_next() from a DO block run by pljs.execute() added rows to
   * the set of the function that ran it.
   */
  pljs_inline_run run = {.source = sourcecode, .ctx = ctx};

  pljs_run_with_storage(ctx, &local_func, fcinfo, false, inline_run, &run);

  SPI_finish();
}

/**
 * @brief Call a Javascript function.
 *
 * Calls a Javascript function returning the result on success, or throwing
 * an error on exception.
 *
 * @returns #Datum of type `VOID`
 */
Datum pljs_call_validator(PG_FUNCTION_ARGS) {
  /*
   * A language validator is called as validator(oid_of_function_being_created),
   * so the function to check is the ARGUMENT.  This used to read
   * fcinfo->flinfo->fn_oid, which is the validator's *own* OID: it fetched the
   * validator's pg_proc row, whose prosrc is the C symbol name
   * "pljs_call_validator".  That happens to parse as a bare JavaScript
   * identifier, so validation always succeeded and an invalid body was accepted
   * silently --
   *
   *   CREATE FUNCTION f() RETURNS int AS $$ this is ( not js $$ LANGUAGE pljs;
   *   CREATE FUNCTION
   *
   * -- with the syntax error surfacing only on the first call.
   *
   * Correcting the OID is necessary but not sufficient: a pljs body is a
   * function *body*, not a program, so `return 42;` is a syntax error at top
   * level and validating the raw prosrc rejects almost every valid function. It
   * has to be wrapped the way compilation wraps it, which is why the source
   * builder is shared with pljs_compile_function().
   */
  Oid fn_oid = PG_GETARG_OID(0);
  HeapTuple proctuple;
  Form_pg_proc functup;
  JSContext *volatile ctx = NULL;
  pljs_context context = {0};
  StringInfoData src;
  volatile bool is_trigger = false;

  if (!CheckFunctionValidatorAccess(fcinfo->flinfo->fn_oid, fn_oid)) {
    PG_RETURN_VOID();
  }

  pljs_encoding_init();

  /* check_function_bodies = off means "create it, do not compile it". */
  if (!check_function_bodies) {
    pljs_cache_function_remove(fn_oid);
    PG_RETURN_VOID();
  }

  proctuple = SearchSysCache(PROCOID, ObjectIdGetDatum(fn_oid), 0, 0, 0);

  if (!HeapTupleIsValid(proctuple)) {
    elog(ERROR, "cache lookup failed for function %u", fn_oid);
  }

  functup = (Form_pg_proc)GETSTRUCT(proctuple);

  /*
   * Check that return and argument types are not disallowed pseudo-types.
   */
  for (int i = -1; i < functup->proargtypes.dim1; i++) {
    Oid typid =
        (i == -1) ? functup->prorettype : functup->proargtypes.values[i];
    char typtype = get_typtype(typid);

    if (typtype == TYPTYPE_PSEUDO) {
      if (i == -1 && (typid == TRIGGEROID
#ifdef OPAQUEOID
                      || (typid == OPAQUEOID && functup->pronargs == 0)
#endif
                          )) {
        is_trigger = true;
      } else if (typid != RECORDOID && typid != RECORDARRAYOID &&
                 typid != VOIDOID && typid != INTERNALOID &&
                 typid != LANGUAGE_HANDLEROID && !IsPolymorphicType(typid) &&
                 !(i >= 0 && typid == ANYOID)) {
        ReleaseSysCache(proctuple);
        ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                 errmsg("PL/JS functions cannot %s type %s",
                        i == -1 ? "return" : "accept", format_type_be(typid))));
      }
    }
  }

  /*
   * Fills in proname, prosrc and the argument names, which the wrapper needs.
   * Passing NULL fcinfo is the same thing pljs_find_js_function() does.
   *
   * Before the context is created: building the source converts it to UTF-8,
   * which can raise, and the context was lost when it did.
   */
  if (!setup_function(NULL, proctuple, &context)) {
    ReleaseSysCache(proctuple);
    PG_RETURN_VOID();
  }

  Oid prolang = functup->prolang;
  Oid owner_id = functup->proowner;
  ReleaseSysCache(proctuple);

  HeapTuple langtuple =
      SearchSysCache(LANGOID, ObjectIdGetDatum(prolang), 0, 0, 0);
  if (!HeapTupleIsValid(langtuple)) {
    elog(ERROR, "cache lookup failed for language %u", prolang);
  }
  bool lang_is_pljs =
      (strcmp(NameStr(((Form_pg_language)GETSTRUCT(langtuple))->lanname),
              "pljs") == 0);
  ReleaseSysCache(langtuple);

  if (!lang_is_pljs) {
    pljs_type_io_cache *types = pljs_type_io_enter(fcinfo->flinfo);
    PG_TRY();
    {
      ctx = pljs_get_context(GetUserId(), owner_id);
      context.ctx = ctx;
      if (!pljs_transpile_if_needed(&context, prolang)) {
        elog(ERROR, "failed to transpile function source code");
      }
      if (context.function->is_srf && OidIsValid(fn_oid)) {
        pljs_ensure_proc_support(fn_oid);
      }
    }
    PG_FINALLY();
    {
      pljs_type_io_exit(types);
    }
    PG_END_TRY();
  }

  bool is_module = pljs_build_function_source(&src, &context, is_trigger);

  ctx = JS_NewContext(rt);
  if (ctx == NULL) {
    pfree(src.data);
    elog(ERROR, "could not create a JavaScript context");
  }
  context.ctx = ctx;

  /*
   * Only the syntax is checked.  A function's imports are not loaded here, so
   * a function can be created before the modules it uses are.  Always use a
   * temporary JSContext so syntax_check_only stub modules are never registered
   * in the user's persistent context.
   */
  JSValue val =
      is_module
          ? pljs_module_eval_source(ctx, src.data, strlen(src.data),
                                    "<function>", true)
          : JS_Eval(ctx, src.data, strlen(src.data), "<function>",
                    JS_EVAL_FLAG_COMPILE_ONLY);

  pfree(src.data);

  if (JS_IsException(val)) {
    pljs_js_error_info errinfo;
    dump_error_ex(ctx, &errinfo);

    /*
     * dump_error_ex() has copied what we need into palloc'd memory, so release the
     * JavaScript side before reporting.  Without this a rejected body leaked
     * the whole context: JS_FreeContext() will not free one that still has live
     * references into it.
     */
    JS_FreeValue(ctx, val);
    JS_FreeContext(ctx);

    pljs_ereport_js_error_info(&errinfo, "invalid pljs function body");
  }

  JS_FreeValue(ctx, val);
  JS_FreeContext(ctx);

  /*
   * The function is being created or replaced, so drop the compiled copy cached
   * for it -- just that entry, in every user's cache.
   *
   * This was previously a blanket pljs_cache_reset(), which destroys every
   * per-user JSContext and rebuilds it on the next call.  JS_FreeContext() will
   * not free a context that still has live references into it, so the old one
   * was not necessarily reclaimed and a backend doing repeated DDL grew without
   * bound.
   */
  pljs_cache_function_remove(fn_oid);

  PG_RETURN_VOID();
}

/**
 * @brief Compile a javascript function and return a pointer to it.
 *
 * Sets up the arguments and code of a javascript function, compiles
 * it, and returns the function itself for use.
 *
 * @param context #pljs_context - context to compile it into, which
 * also has the current function
 * @param is_trigger #bool - whether it is to be called as a trigger
 * or not, this determines arguments
 * @returns #JSValue of the compiled function
 */
/*
 * Build the JavaScript source for a pljs function: its body wrapped in a named
 * function with the declared argument names, followed by a reference to it so
 * the evaluation yields the function object.
 *
 * Extracted so that pljs_call_validator() can check exactly what
 * pljs_compile_function() will later compile.  A pljs body is a function
 * *body*, not a program -- `return 42;` is a syntax error at top level -- so
 * validating the raw prosrc rejects almost every valid function.  Sharing this
 * makes the two agree by construction rather than by two copies staying in
 * step.
 *
 * A body that starts with `import` statements is built as a module instead:
 * the imports go first, on the first line so that nothing after them moves,
 * and the function is declared in the module, made a global as a script's
 * would be, and exported as the default.
 *
 * The returned StringInfo's data is palloc'd; the caller frees it.
 *
 * @returns @c bool - whether the source is a module
 */
static bool pljs_build_function_source(StringInfoData *src,
                                       pljs_context *context, bool is_trigger) {
  int i;
  StringInfoData imports, body;
  bool is_module;
  char *proname = pljs_server_to_utf8(context->function->proname,
                                      strlen(context->function->proname));

  initStringInfo(&imports);
  initStringInfo(&body);
  is_module = pljs_extract_static_imports(context->function->prosrc, &imports,
                                          &body);

  initStringInfo(src);

  // the imports of a module come first
  appendStringInfoString(src, imports.data);

  // generate the function as javascript with all of its arguments
  appendStringInfo(src, "function %s (", proname);

  int inarg = 0;
  for (i = 0; i < context->function->nargs; i++) {
    /*
     * Every argument but an OUT one.  A RETURNS TABLE column is a parameter
     * too, which the call leaves undefined: bodies assign to them, as to
     * variables of their own, and left out they became globals of the user's
     * context, or failed in strict mode.
     */
    if (context->function->argmodes[i] == PROARGMODE_OUT) {
      continue;
    }
    // commas between arguments
    if (inarg > 0) {
      appendStringInfoChar(src, ',');
    }

    // if this is a named argument, append it
    if (context->arguments[i]) {
      appendStringInfoString(src, context->arguments[i]);
    } else {
      // otherwise append it as an unnamed argument with a number
      appendStringInfo(src, "$%d", inarg + 1);
    }

    inarg++;
  }

  // append the other postgres-specific variables as well
  if (context->function->inargs && is_trigger) {
    appendStringInfo(src, ", ");
  }

  if (is_trigger) {
    appendStringInfo(src, "NEW, OLD, TG_NAME, TG_WHEN, TG_LEVEL, TG_OP, "
                          "TG_RELID, TG_TABLE_NAME, TG_TABLE_SCHEMA, TG_ARGV");
  }

  appendStringInfo(src, ") {\n%s\n}\n", body.data);

  if (is_module) {
    appendStringInfo(src, "globalThis.%s = %s;\nexport default %s;\n",
                     proname, proname, proname);
  } else {
    appendStringInfo(src, " %s;\n", proname);
  }

  pfree(imports.data);
  pfree(body.data);

  if (proname != context->function->proname) {
    pfree(proname);
  }

  return is_module;
}

/**
 * @brief Compiles a function, running any code at the top level of its source.
 *
 * A body can close the function it is wrapped in -- `} code(); function x() {`
 * -- and the code between runs as the source is compiled, before any call.  It
 * gets storage of its own, as a pljs.start_proc does, with no set to return
 * and no window.  It ran with none at all on a function's first call from a
 * query, where a failed commit of a subtransaction it started crashed the
 * backend, and with the storage of the call that compiled it on one from
 * inside another call, where its return_next() added rows to that call's set.
 *
 * @param context #pljs_context - the function
 * @param is_trigger @c bool - whether it is a trigger
 * @returns #JSValue of the compiled function
 */
/* What pljs_run_with_storage() runs for pljs_compile_function(). */
typedef struct pljs_compile_run {
  pljs_context *context;
  StringInfoData src;
  bool is_module;
  JSValue val;
} pljs_compile_run;

/**
 * @brief Compiles a function's source; see pljs_compile_function().
 *
 * @param arg #pljs_compile_run - the function and its source, which is freed;
 * its val is set
 */
static void compile_run(void *arg) {
  pljs_compile_run *run = (pljs_compile_run *)arg;
  JSContext *ctx = run->context->ctx;
  JSValue val;

  if (run->is_module) {
    /*
     * The modules it imports are bound now, so note which generation of them
     * these are before loading any; see pljs_modules_generation().
     */
    run->context->function->module_generation = pljs_modules_generation();

    JSValue ns = pljs_module_eval_source(ctx, run->src.data,
                                         strlen(run->src.data), "<function>",
                                         false);

    if (JS_IsException(ns)) {
      val = ns;
    } else {
      val = JS_GetPropertyStr(ctx, ns, "default");
      JS_FreeValue(ctx, ns);
    }
  } else {
    val = JS_Eval(ctx, run->src.data, strlen(run->src.data), "<function>", 0);
  }

  pfree(run->src.data);

  if (JS_IsException(val)) {
    pljs_js_error_info errinfo;
    dump_error_ex(ctx, &errinfo);

    /* Surface a pending cancel/terminate as the real PostgreSQL error. */
    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "execution error");
  }

  /* Its call ends with an error all the same; see pljs_run_with_storage(). */
  if (current_storage->fatal_error != NULL) {
    JS_FreeValue(ctx, val);
    return;
  }

  run->val = val;
}

JSValue pljs_compile_function(pljs_context *context, bool is_trigger) {
  pljs_compile_run run = {.context = context, .val = JS_UNDEFINED};

  if (!pljs_transpile_if_needed(context, InvalidOid)) {
    elog(ERROR, "failed to transpile function source code");
  }
  if (context->function->nhandlers > 0 && context->function->is_srf &&
      OidIsValid(context->function->fn_oid)) {
    pljs_ensure_proc_support(context->function->fn_oid);
    HeapTuple upd_tup = SearchSysCache1(
        PROCOID, ObjectIdGetDatum(context->function->fn_oid));
    if (HeapTupleIsValid(upd_tup)) {
      context->function->fn_xmin = HeapTupleHeaderGetRawXmin(upd_tup->t_data);
      context->function->fn_tid = upd_tup->t_self;
      ReleaseSysCache(upd_tup);
    }
  }

  context->function->module_generation = 0;
  run.is_module = pljs_build_function_source(&run.src, context, is_trigger);
  pljs_run_with_storage(context->ctx, NULL, NULL, true, compile_run, &run);

  return run.val;
}

/**
 * @brief Compile and call an anonymous function.
 *
 * Compiles an anonymous function inside the #JSContext passed, then
 * executes it within the context passed.
 *
 * @param source @c char * - the source code of the function to compile
 * @param ctx #JSContext - the Javascript context to compile and execute in
 */
static void call_anonymous_function(const char *source, JSContext *ctx) {
  StringInfoData src, imports, body;

  initStringInfo(&src);
  initStringInfo(&imports);
  initStringInfo(&body);

  /*
   * A block that starts with `import` statements is run as a module, with the
   * imports first.
   */
  bool is_module = pljs_extract_static_imports(source, &imports, &body);

  // generate the function as javascript with all of its arguments
  appendStringInfo(&src, "%s(function () {%s})();", imports.data, body.data);
  pfree(imports.data);
  pfree(body.data);

  /*
   * Re-anchor QuickJS's stack measurement here, at the C-stack depth this call
   * actually starts from.  JS_NewRuntime() records the stack top once, inside
   * _PG_init, at whatever depth the first pljs call happened to be -- but JS
   * can run far deeper than that (SQL -> JS -> pljs.execute -> SQL -> JS ->
   * ...), so a budget measured from the original anchor does not describe the
   * stack this call has left.  The vendored QuickJS exports JS_UpdateStackTop()
   * for exactly this.
   */
  JS_UpdateStackTop(JS_GetRuntime(ctx));

  JSValue val;

  if (is_module) {
    val = pljs_module_eval_source(ctx, src.data, strlen(src.data), "<function>",
                                  false);
  } else {
    val = JS_Eval(ctx, src.data, strlen(src.data), "<function>", 0);
  }

  if (!JS_IsException(val)) {
    JS_FreeValue(ctx, val);
    pfree(src.data);
  } else {
    /*
     * Extract the error, release everything, then report.  The report never
     * returns, so anything freed after it is dead code -- and `val` was never
     * released on this path at all, leaking a QuickJS reference for every
     * failed DO block.
     */
    pljs_js_error_info errinfo;
    dump_error_ex(ctx, &errinfo);

    JS_FreeValue(ctx, val);
    pfree(src.data);

    /*
     * If QuickJS aborted because a cancel/terminate is pending, raise the real
     * PostgreSQL error (canceling statement / terminating connection) now that
     * we are safely back in C, instead of the generic JS interrupt message.
     * After the cleanup above, so a cancel cannot skip it.
     */
    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "execution error");
  }
}

/**
 * @brief Call a trigger.
 *
 * Sets up all of the function arguments for a trigger, and calls
 * a trigger function.  This also determines the result type and
 * generates a resulting return Datum for postgres to injest.
 *
 * @param fcinfo #FunctionCallInfo
 * @param context #pljs_context
 * @returns #Datum containing the return value from the trigger
 */
static Datum call_trigger(FunctionCallInfo fcinfo, pljs_context *context) {
  TriggerData *trig = (TriggerData *)fcinfo->context;
  Relation rel = trig->tg_relation;
  TriggerEvent event = trig->tg_event;
  Datum result = (Datum)0;

  MemoryContext execution_context = AllocSetContextCreate(
      CurrentMemoryContext, "PLJS Trigger Memory Context (call_trigger)",
      ALLOCSET_SMALL_SIZES);
  MemoryContext old_context = MemoryContextSwitchTo(execution_context);

  /*
   * Every argument is undefined until it is made, and all of them are released
   * if one cannot be: an OLD that did not convert, once NEW had, left NEW in
   * the runtime for every attempt.  Allocated rather than on the stack, so the
   * PG_CATCH reads what the PG_TRY wrote.
   */
  JSValueConst *argv = palloc(sizeof(JSValueConst) * 10);

  for (int i = 0; i < 10; i++) {
    argv[i] = JS_UNDEFINED;
  }

  if (TRIGGER_FIRED_FOR_ROW(event)) {
    result =
        PointerGetDatum(TRIGGER_FIRED_BY_UPDATE(event) ? trig->tg_newtuple
                                                       : trig->tg_trigtuple);
  }

  PG_TRY();
  {
    if (TRIGGER_FIRED_FOR_ROW(event)) {
      TupleDesc tupdesc = RelationGetDescr(rel);

      if (TRIGGER_FIRED_BY_INSERT(event)) {
        // NEW
        argv[0] =
            pljs_tuple_to_jsvalue(tupdesc, trig->tg_trigtuple, context->ctx);
      } else if (TRIGGER_FIRED_BY_DELETE(event)) {
        // OLD
        argv[1] =
            pljs_tuple_to_jsvalue(tupdesc, trig->tg_trigtuple, context->ctx);
      } else if (TRIGGER_FIRED_BY_UPDATE(event)) {
        // NEW
        argv[0] =
            pljs_tuple_to_jsvalue(tupdesc, trig->tg_newtuple, context->ctx);
        // OLD
        argv[1] =
            pljs_tuple_to_jsvalue(tupdesc, trig->tg_trigtuple, context->ctx);
      }
    }

    /*
     * Names and arguments in UTF-8, as QuickJS reads them; see
     * pljs_server_to_utf8().
     */
    const char *name = trig->tg_trigger->tgname;

    // 2: TG_NAME
    argv[2] = pljs_new_server_string(context->ctx, name, strlen(name));

    // 3: TG_WHEN
    if (TRIGGER_FIRED_BEFORE(event)) {
      argv[3] = JS_NewString(context->ctx, "BEFORE");
    } else {
      argv[3] = JS_NewString(context->ctx, "AFTER");
    }
    // 4: TG_LEVEL
    if (TRIGGER_FIRED_FOR_ROW(event)) {
      argv[4] = JS_NewString(context->ctx, "ROW");
    } else {
      argv[4] = JS_NewString(context->ctx, "STATEMENT");
    }

    // 5: TG_OP
    if (TRIGGER_FIRED_BY_INSERT(event)) {
      argv[5] = JS_NewString(context->ctx, "INSERT");
    } else if (TRIGGER_FIRED_BY_DELETE(event)) {
      argv[5] = JS_NewString(context->ctx, "DELETE");
    } else if (TRIGGER_FIRED_BY_UPDATE(event)) {
      argv[5] = JS_NewString(context->ctx, "UPDATE");
    } else if (TRIGGER_FIRED_BY_TRUNCATE(event)) {
      argv[5] = JS_NewString(context->ctx, "TRUNCATE");
    } else {
      argv[5] = JS_NewString(context->ctx, "?");
    }

    // 6: TG_RELID, unsigned: an OID of 2^31 or more was a negative number.
    argv[6] = JS_NewUint32(context->ctx, RelationGetRelid(rel));

    // 7: TG_TABLE_NAME
    name = RelationGetRelationName(rel);
    argv[7] = pljs_new_server_string(context->ctx, name, strlen(name));

    // 8: TG_TABLE_SCHEMA
    name = get_namespace_name(RelationGetNamespace(rel));
    argv[8] = pljs_new_server_string(context->ctx, name, strlen(name));

    // 9: TG_ARGV
    argv[9] = JS_NewArray(context->ctx);

    for (int i = 0; i < trig->tg_trigger->tgnargs; i++) {
      name = trig->tg_trigger->tgargs[i];

      /* Defined, not set; see pljs_datum_to_object(). */
      JS_DefinePropertyValueUint32(
          context->ctx, argv[9], i,
          pljs_new_server_string(context->ctx, name, strlen(name)),
          JS_PROP_C_W_E);
    }
  }
  PG_CATCH();
  {
    for (int i = 0; i < 10; i++) {
      JS_FreeValue(context->ctx, argv[i]);
    }

    PG_RE_THROW();
  }
  PG_END_TRY();

  /*
   * Connect to SPI, which call_trigger() never did -- so pljs.execute(),
   * pljs.prepare() and every other SPI entry point failed inside a trigger. Not
   * just DDL: a bare pljs.execute("SELECT 1") in a BEFORE INSERT trigger failed
   * too.  Upstream reports it as "execution error"; the error-surfacing work in
   * this series turns it into the underlying "current transaction is aborted",
   * which is what made it findable.
   *
   * Atomic unconditionally: a trigger has no CallContext, so there is no
   * nonatomic case to honour, and a trigger must not be able to commit.
   */
  if (SPI_connect_ext(0) != SPI_OK_CONNECT) {
    elog(ERROR, "could not connect to spi manager");
  }

  /*
   * Re-anchor QuickJS's stack measurement here, at the C-stack depth this call
   * actually starts from.  JS_NewRuntime() records the stack top once, inside
   * _PG_init, at whatever depth the first pljs call happened to be -- but JS
   * can run far deeper than that (SQL -> JS -> pljs.execute -> SQL -> JS ->
   * ...), so a budget measured from the original anchor does not describe the
   * stack this call has left.  The vendored QuickJS exports JS_UpdateStackTop()
   * for exactly this.
   */
  JS_UpdateStackTop(JS_GetRuntime(context->ctx));

  /*
   * Hold a reference of our own for the call.  The cache owns the function and
   * drops it when it goes stale -- a module it imports changed, say, seen by a
   * nested call of the same function -- and a function that is running must
   * not be freed under itself.
   */
  JSValue running = JS_DupValue(context->ctx, context->js_function);
  JSValue ret = JS_Call(context->ctx, running, JS_UNDEFINED, 10, argv);

  JS_FreeValue(context->ctx, running);

  /* JS_Call() took references of its own; see dispatch_call(). */
  for (int i = 0; i < 10; i++) {
    JS_FreeValue(context->ctx, argv[i]);
  }

  if (JS_IsException(ret)) {
    /*
     * Same order as call_function(): extract, release, then report.  The
     * JS_FreeValue() below used to sit *after* the report, which never returns,
     * so it was dead code -- `ret` leaked a QuickJS reference on every trigger
     * exception, not merely on a cancel.
     *
     * The error is extracted while the SPI connection is open, as the result
     * is converted; see call_function().
     */
    pljs_js_error_info errinfo;

    MemoryContextSwitchTo(execution_context);
    dump_error_ex(context->ctx, &errinfo);

    JS_FreeValue(context->ctx, ret);

    /* Before the report, which does not return. */
    SPI_finish();

    MemoryContextSwitchTo(old_context);

    /* Surface a pending cancel/terminate as the real PostgreSQL error. */
    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "execution error");
  }

  /*
   * Convert NEW while the SPI connection is open, and release it however that
   * ends; see call_function().
   */
  MemoryContextSwitchTo(execution_context);

  PG_TRY();
  {
    pljs_raise_if_ending();

    if (JS_IsNull(ret) || !TRIGGER_FIRED_FOR_ROW(event)) {
      result = PointerGetDatum(NULL);
    } else if (!JS_IsUndefined(ret)) {

      TupleDesc tupdesc = RelationGetDescr(rel);

      pljs_type type;
      pljs_type_fill(&type, context->function->rettype);
      Datum d = pljs_jsvalue_to_record(&type, ret, NULL, tupdesc, context->ctx);

      HeapTupleHeader header = DatumGetHeapTupleHeader(d);

      result = PointerGetDatum((char *)header - HEAPTUPLESIZE);
    }
  }
  PG_FINALLY();
  {
    JS_FreeValue(context->ctx, ret);
  }
  PG_END_TRY();

  SPI_finish();

  MemoryContextSwitchTo(old_context);
  return result;
}

/**
 * @brief Call a Javascript function.
 *
 * Calls a Javascript function returning the result on success, or throwing
 * an error on exception.
 *
 * @param fcinfo #FunctionCallInfo
 * @param context #pljs_context
 * @param argv #JSValueConst - array of arguments as Javascript values
 * @returns #Datum containing the return value from the function
 */
static Datum call_function(FunctionCallInfo fcinfo, pljs_context *context,
                           JSValueConst *argv) {
  MemoryContext execution_context = AllocSetContextCreate(
      CurrentMemoryContext, "PLJS Function Memory Context (call_function)",
      ALLOCSET_SMALL_SIZES);
  MemoryContext old_context = MemoryContextSwitchTo(execution_context);

  Oid fn_oid = fcinfo->flinfo->fn_oid;
  HeapTuple proctuple =
      SearchSysCache(PROCOID, ObjectIdGetDatum(fn_oid), 0, 0, 0);

  Oid rettype;
  Form_pg_proc pg_proc_entry = (Form_pg_proc)GETSTRUCT(proctuple);

  if (fcinfo && IsPolymorphicType(pg_proc_entry->prorettype)) {
    rettype = get_fn_expr_rettype(fcinfo->flinfo);
  } else {
    rettype = pg_proc_entry->prorettype;
  }
  ReleaseSysCache(proctuple);

  bool nonatomic = fcinfo->context && IsA(fcinfo->context, CallContext) &&
                   !castNode(CallContext, fcinfo->context)->atomic;
  if (SPI_connect_ext(nonatomic ? SPI_OPT_NONATOMIC : 0) != SPI_OK_CONNECT) {
    elog(ERROR, "could not connect to spi manager");
  }

  /*
   * Re-anchor QuickJS's stack measurement here, at the C-stack depth this call
   * actually starts from.  JS_NewRuntime() records the stack top once, inside
   * _PG_init, at whatever depth the first pljs call happened to be -- but JS
   * can run far deeper than that (SQL -> JS -> pljs.execute -> SQL -> JS ->
   * ...), so a budget measured from the original anchor does not describe the
   * stack this call has left.  The vendored QuickJS exports JS_UpdateStackTop()
   * for exactly this.
   */
  JS_UpdateStackTop(JS_GetRuntime(context->ctx));

  // Held for the call; see call_trigger().
  JSValue running = JS_DupValue(context->ctx, context->js_function);
  JSValue ret = JS_Call(context->ctx, running, JS_UNDEFINED,
                        context->function->inargs, argv);

  JS_FreeValue(context->ctx, running);

  if (JS_IsException(ret)) {
    pljs_js_error_info errinfo;

    /*
     * Extract the error while the SPI connection is still open, for the same
     * reason the result is converted then: dump_error_ex() runs JavaScript -- the
     * thrown value's toString(), and getters for its message, detail and
     * sqlstate -- and pljs.commit() from there crashed the backend after
     * SPI_finish().  It is extracted into this call's context, which outlives
     * SPI_finish(), rather than SPI's.
     */
    MemoryContextSwitchTo(execution_context);
    dump_error_ex(context->ctx, &errinfo);

    JS_FreeValue(context->ctx, ret);

    /* Before the report, which does not return. */
    SPI_finish();

    /* Surface a pending cancel/terminate as the real PostgreSQL error. */
    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "execution error");

    /* Shuts up the compiler, since ereports of ERROR stop execution. */
    return (Datum)0;
  } else {
    Datum datum = 0;
    bool was_converting = pljs_converting_result;

    /*
     * Convert the result while this call's SPI connection is still open, as
     * PL/pgSQL does.  The conversion can run JavaScript -- a getter, or
     * toString(), on what the function returned -- and that can call
     * pljs.execute() or pljs.commit().  After SPI_finish() those ran with no
     * connection, where pljs.commit() crashed the backend, or on the caller's,
     * such as that of the PL/pgSQL function whose query called this one.
     *
     * The result has to outlive SPI_finish(), so it is built in this call's
     * own context rather than SPI's.  A procedure still cannot end its
     * transaction from here; see pljs_commit().
     *
     * The result is released however the conversion ends.  A result that
     * could not be converted -- one bad element of a large array -- stayed in
     * the runtime for the life of the backend, and a loop that retried the
     * call ran pljs.memory_limit out.
     */
    MemoryContextSwitchTo(execution_context);
    pljs_converting_result = true;

    PG_TRY();
    {
      datum = convert_result(fcinfo, context, rettype, ret);
    }
    PG_FINALLY();
    {
      pljs_converting_result = was_converting;
      JS_FreeValue(context->ctx, ret);
    }
    PG_END_TRY();

    SPI_finish();

    MemoryContextSwitchTo(old_context);

    return datum;
  }
}

/**
 * @brief Converts what a function returned to its result type.
 *
 * @param fcinfo #FunctionCallInfo - the call
 * @param context #pljs_context - the function
 * @param rettype #Oid - the result type
 * @param ret #JSValue - what the function returned
 * @returns #Datum of the result, with fcinfo->isnull set for a SQL NULL
 */
static Datum convert_result(FunctionCallInfo fcinfo, pljs_context *context,
                            Oid rettype, JSValue ret) {
  Datum datum;

  pljs_raise_if_ending();

  if (rettype == RECORDOID) {
    TupleDesc tupdesc;

    /*
     * Check the status rather than discarding it.  TYPEFUNC_RECORD means the
     * caller did not supply a column definition list, and tupdesc comes back
     * NULL; pljs_jsvalue_to_record() then reached
     * lookup_rowtype_tupdesc(RECORDOID, -1) and raised "record type has not
     * been registered", which is an unhelpful way to say "you forgot
     * AS (a int, b text)".
     */
    if (get_call_result_type(fcinfo, &rettype, &tupdesc) !=
        TYPEFUNC_COMPOSITE) {
      ereport(ERROR,
              (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
               errmsg("a function returning \"record\" needs a column "
                      "definition list"),
               errhint("Call it as ... AS (column_name data_type, ...).")));
    }

    pljs_type type;
    bool is_null = false;

    pljs_type_fill(&type, rettype);

    /*
     * pljs_jsvalue_to_record() reports a null or undefined result through
     * is_null, and was handed NULL for it: `return null` from a function
     * returning record, or with OUT parameters, crashed the backend.
     */
    datum = pljs_jsvalue_to_record(&type, ret, &is_null, tupdesc, context->ctx);

    if (is_null) {
      fcinfo->isnull = true;
    }
  } else {
    bool is_null;
    datum = pljs_jsvalue_to_datum(rettype, ret, &is_null, context->ctx, fcinfo);
  }

  return datum;
}

/**
 * @brief Puts a row that a set-returning function returned into its result.
 *
 * A row of a composite set is a `{column: value}` object.  A row of a
 * single-column set is its value, or an object naming it, as return_next()
 * accepts; see pljs_single_column_value().
 *
 * @param state #pljs_return_state - the set being returned
 * @param row #JSValueConst - the row
 * @param ctx #JSContext - Javascript context to execute in
 */
static void put_returned_row(pljs_return_state *state, JSValueConst row,
                             JSContext *ctx) {
  pljs_raise_if_ending();
  /* A getter on the returned array that threw. */
  if (JS_IsException(row)) {
    pljs_ereport_js_exception(ctx);
  }

  /*
   * A row of a composite set is an object naming every column, as
   * return_next() requires, which is checked as it is converted.  Anything
   * else but null was stored as a row of NULLs: `return [5, 'oops']`.
   */
  if (state->is_composite && !JS_IsNull(row) && !JS_IsUndefined(row) &&
      !JS_IsObject(row)) {
    ereport(ERROR, (errcode(ERRCODE_DATATYPE_MISMATCH),
                    errmsg("returned row must be an object")));
  }

  if (state->is_domain) {
    if (!JS_IsNull(row) && !JS_IsUndefined(row)) {
      pljs_put_domain_row(state, row, ctx, "returned row");
    } else {
      /*
       * A null row is left out, as it is for any other composite set -- but
       * only once the domain has allowed it, as return_next() checks one.  A
       * NOT NULL domain's set could return null rows and have them dropped
       * without a word.
       */
      bool is_null;

      pljs_jsvalue_to_datum(state->rettype, row, &is_null, ctx, NULL);
    }
  } else if (state->is_composite) {
    bool *nulls = (bool *)palloc0(sizeof(bool) * state->tuple_desc->natts);
    Datum *values = pljs_jsvalue_to_datums(NULL, row, &nulls, state->tuple_desc,
                                           ctx, "returned row");

    if (values != NULL) {
      tuplestore_putvalues(state->tuple_store_state, state->tuple_desc, values,
                           nulls);
      pfree(values);
    }

    pfree(nulls);
  } else {
    JSValue value = pljs_single_column_value(ctx, row, state, "returned row");
    bool is_null = false;
    Datum result;

    if (JS_IsException(value)) {
      pljs_ereport_js_exception(ctx);
    }

    result = pljs_jsvalue_to_datum_free(
        TupleDescAttr(state->tuple_desc, 0)->atttypid, value, &is_null, ctx);

    tuplestore_putvalues(state->tuple_store_state, state->tuple_desc, &result,
                         &is_null);
  }
}

/**
 * @brief Puts a row that a set-returning function returned, and releases it.
 *
 * The row is released however putting it ends.  It is a parameter here,
 * rather than a variable of the caller's loop, because a variable assigned in
 * a PG_TRY cannot be relied on in its PG_FINALLY even when it is volatile:
 * clang reads a volatile JSValue passed by value from the register it was
 * last in, and the row that failed was never released.
 *
 * @param state #pljs_return_state - the set being returned
 * @param row #JSValue - the row, an owned reference, which is released
 * @param ctx #JSContext - Javascript context to execute in
 */
static void put_returned_row_free(pljs_return_state *state, JSValue row,
                                  JSContext *ctx) {
  PG_TRY();
  {
    put_returned_row(state, row, ctx);
  }
  PG_FINALLY();
  {
    JS_FreeValue(ctx, row);
  }
  PG_END_TRY();
}

/**
 * @brief Call a set returning function (SRF).
 *
 * Sets up all of the function arguments for a set returning function,
 * and calls it.  Generally output is returned with `pljs.return_next()`,
 * but if there are additional results returned, then they are appended
 * as well.  This also determines the result type and generates a resulting
 * return Datum for postgres to injest.
 *
 * @param fcinfo #FunctionCallInfo
 * @param context #pljs_context
 * @param argv #JSValueConst - array of arguments as Javascript values
 * @returns #Datum containing the return value from the function
 */
static Datum call_srf_function(FunctionCallInfo fcinfo, pljs_context *context,
                               JSValueConst *argv) {
  pljs_return_state *state = NULL;
  MemoryContext execution_context = AllocSetContextCreate(
      CurrentMemoryContext,
      "PLJS Set Returning Memory Context (call_srf_function)",
      ALLOCSET_SMALL_SIZES);
  MemoryContext old_context = MemoryContextSwitchTo(execution_context);

  bool nonatomic = fcinfo->context && IsA(fcinfo->context, CallContext) &&
                   !castNode(CallContext, fcinfo->context)->atomic;
  if (SPI_connect_ext(nonatomic ? SPI_OPT_NONATOMIC : 0) != SPI_OK_CONNECT) {
    elog(ERROR, "could not connect to spi manager");
  }

  ReturnSetInfo *rsinfo = (ReturnSetInfo *)fcinfo->resultinfo;

  if (rsinfo == NULL || !IsA(rsinfo, ReturnSetInfo)) {
    ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("set-valued function called in context that cannot "
                           "accept a set")));
  }

  if (!(rsinfo->allowedModes & SFRM_Materialize)) {
    ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("materialize mode required, but it is not "
                           "allowed in this context")));
  }

  MemoryContextSwitchTo(rsinfo->econtext->ecxt_per_query_memory);

  TypeFuncClass typeclass;

  /*
   * Only the set itself, and its descriptor, have to outlive the call.  The
   * state was kept with them, for as long as the query ran: a set-returning
   * function called once for each row of a LATERAL join left one for every
   * row.
   */
  state = (pljs_return_state *)MemoryContextAlloc(execution_context,
                                                  sizeof(pljs_return_state));

  /*
   * The result type is resolved for this call rather than taken from the
   * function's cache entry.  A polymorphic function -- SETOF anyelement --
   * returns a different type at each call site, and the class its first call
   * resolved to was kept for every later one: after f(1), f(ROW(1, 2)::pair)
   * was put as a single column, and the tuplestore read the second off the
   * stack.  The check for a record read its return type from the cache entry
   * too, which never copied it, so every cached call compared uninitialized
   * memory.
   *
   * No descriptor is asked for, which would be a copy of the row type made in
   * the query's memory for every call; the set's is rsinfo's.
   */
  typeclass = get_call_result_type(fcinfo, &state->rettype, NULL);

  bool has_concrete_expected_desc =
      (rsinfo->expectedDesc != NULL && rsinfo->expectedDesc->natts > 0 &&
       TupleDescAttr(rsinfo->expectedDesc, 0)->atttypid != RECORDOID);

  /* A record with no column definition list to say what its columns are. */
  if ((typeclass == TYPEFUNC_RECORD && !has_concrete_expected_desc) ||
      rsinfo->expectedDesc == NULL) {
    ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("function returning record called in context "
                           "that cannot accept type record")));
  }

  state->tuple_store_state = tuplestore_begin_heap(true, false, work_mem);

  if (!rsinfo->setDesc) {
    state->tuple_desc = CreateTupleDescCopy(rsinfo->expectedDesc);
    rsinfo->setDesc = state->tuple_desc;
  } else {
    state->tuple_desc = rsinfo->setDesc;
  }

  /*
   * A set of a domain over a composite type has rows of the composite type,
   * each of which has to satisfy the domain.  TYPEFUNC_COMPOSITE_DOMAIN was
   * taken for a single-column set, so its row objects had their first
   * property converted, and that one Datum was passed as a row of all of the
   * composite type's columns: tuplestore_putvalues() read the rest off the
   * stack, and the backend was killed.  The domain's constraints were never
   * checked either.
   */
  state->is_domain = typeclass == TYPEFUNC_COMPOSITE_DOMAIN;
  state->is_composite = typeclass == TYPEFUNC_COMPOSITE || state->is_domain ||
                        (typeclass == TYPEFUNC_RECORD &&
                         has_concrete_expected_desc &&
                         state->tuple_desc->natts > 1);
  state->row_context =
      state->is_domain
          ? AllocSetContextCreate(execution_context, "PLJS Domain Row",
                                  ALLOCSET_SMALL_SIZES)
          : NULL;
  state->row_context_busy = false;
  state->domain_map_known = false;
  state->domain_rowtype_id = 0;
  state->domain_context = NULL;
  state->domain_rowtype = NULL;
  state->domain_map = NULL;

  /*
   * A single-column set's column is named when a row object first needs it;
   * see pljs_single_column_value().
   */
  state->fn_oid = fcinfo->flinfo->fn_oid;
  state->column_known = false;
  state->column_name = NULL;
  state->column_atom = JS_ATOM_NULL;
  state->column_type_known = false;
  state->column_takes_objects = false;

  /*
   * Whether converting a row can run a domain's CHECK constraint, which can
   * run any SQL, is worked out by pljs_return_next() when it is first called.
   */
  state->convert_in_subtransaction = false;
  state->convert_known = false;
  state->convert_generation = 0;

  rsinfo->returnMode = SFRM_Materialize;
  rsinfo->setResult = state->tuple_store_state;

  MemoryContextSwitchTo(execution_context);

  // Set the current return context.
  pljs_current_storage()->return_state = state;

  /*
   * Re-anchor QuickJS's stack measurement here, at the C-stack depth this call
   * actually starts from.  JS_NewRuntime() records the stack top once, inside
   * _PG_init, at whatever depth the first pljs call happened to be -- but JS
   * can run far deeper than that (SQL -> JS -> pljs.execute -> SQL -> JS ->
   * ...), so a budget measured from the original anchor does not describe the
   * stack this call has left.  The vendored QuickJS exports JS_UpdateStackTop()
   * for exactly this.
   */
  JS_UpdateStackTop(JS_GetRuntime(context->ctx));

  // Held for the call; see call_trigger().
  JSValue running = JS_DupValue(context->ctx, context->js_function);
  JSValue ret = JS_Call(context->ctx, running, JS_UNDEFINED,
                        context->function->inargs, argv);

  JS_FreeValue(context->ctx, running);

  if (JS_IsException(ret)) {
    pljs_js_error_info errinfo;

    /* While the SPI connection is open; see call_function(). */
    MemoryContextSwitchTo(execution_context);
    dump_error_ex(context->ctx, &errinfo);

    JS_FreeValue(context->ctx, ret);

    /* Before the report, which does not return. */
    SPI_finish();

    /* Surface a pending cancel/terminate as the real PostgreSQL error. */
    CHECK_FOR_INTERRUPTS();

    pljs_ereport_js_error_info(&errinfo, "execution error");

    /* Shuts up the compiler, since ereports of ERROR stop execution. */
    return (Datum)0;
  } else {
    /*
     * Rows the function returned rather than passed to return_next() are
     * converted while the SPI connection is open, and released however that
     * ends; see call_function().
     */
    PG_TRY();
    {
      if (!JS_IsUndefined(ret) && !JS_IsNull(ret)) {
        /*
         * In this call's memory, as return_next() converts a row: the
         * tuplestore copies each row into its own.  They were converted in
         * the query's, where what converting them allocated stayed for as long
         * as the query ran -- for every call of a LATERAL join's.
         */
        MemoryContextSwitchTo(execution_context);

        // JS can return a single row or an array of rows.
        if (JS_IsArray(context->ctx, ret)) {
          int32_t length = pljs_js_array_length(ret, context->ctx);

          if (length < 0) {
            pljs_ereport_js_exception(context->ctx);
          }

          for (int32_t i = 0; i < length; i++) {
            put_returned_row_free(state,
                                  JS_GetPropertyUint32(context->ctx, ret, i),
                                  context->ctx);
          }
        } else {
          put_returned_row(state, ret, context->ctx);
        }

        MemoryContextSwitchTo(execution_context);
      }
    }
    PG_FINALLY();
    {
      JS_FreeValue(context->ctx, ret);
    }
    PG_END_TRY();
  }

  SPI_finish();

  // Switch back the original context
  MemoryContextSwitchTo(old_context);

  PG_RETURN_NULL();
}

/**
 * @brief Throws a Javascript exception.
 *
 * Throws a Javascript exception and fills it with the message passed, along
 * with as much context as it can derive from the current state of Postgres
 * when the exception is called.
 *
 * @param message @c const char * - message to throw with
 * @param ctx #JSContext - Javascript context to execute in
 * @returns #JSValue of the exception
 */
JSValue js_throw(const char *message, JSContext *ctx) {
  ErrorData *fatal_error = pljs_fatal_error();

  /* Nothing JavaScript can catch; see pljs_throw_fatal_error(). */
  if (fatal_error != NULL) {
    return js_throw_uncatchable(fatal_error, ctx);
  }

  JSValue error = JS_NewError(ctx);

  /*
   * A message can name a column or a type, in the database's encoding, and
   * QuickJS reads UTF-8; see pljs_server_to_utf8().  So for every message
   * PostgreSQL hands JavaScript.
   */
  JSValue message_value =
      pljs_new_message_string(ctx, message, strlen(message));
  JS_SetPropertyStr(ctx, error, "message", message_value);

  return JS_Throw(ctx, error);
}

/*
 * Makes a JavaScript string of part of a PostgreSQL error, which is in the
 * database's encoding; see js_throw().  NULL is the empty string.
 */
static JSValue js_error_string(JSContext *ctx, const char *text) {
  if (text == NULL) {
    text = "";
  }

  return pljs_new_message_string(ctx, text, strlen(text));
}

/*
 * Throws an exception that no catch or finally block sees, for the error the
 * running call has to end with; see pljs_throw_fatal_error().
 */
static JSValue js_throw_uncatchable(ErrorData *edata, JSContext *ctx) {
  JSValue error = JS_NewError(ctx);

  JS_SetPropertyStr(ctx, error, "message",
                    js_error_string(ctx, edata->message));
  JS_SetUncatchableError(ctx, error, true);

  return JS_Throw(ctx, error);
}

/**
 * @brief Ends the running call with the PostgreSQL error being handled.
 *
 * For a PG_CATCH whose error JavaScript must not catch, because what raised it
 * left behind state that only ending the query cleans up.  A window object's
 * methods run the executor of the query that called the window function -- to
 * read its partition, and to evaluate its arguments, which can call any
 * function -- and a function that raised there left its SPI connection on the
 * stack.  JavaScript caught the error and carried on with that: "transaction
 * left non-empty SPI stack", and a result for one row computed without the
 * row that raised.  Nothing can roll the query back to a savepoint, and
 * re-throwing the error from a function QuickJS called unwinds past its live
 * frames; see pljs_return_next().
 *
 * So the error is kept in the call's storage, and JavaScript gets an exception
 * that no catch or finally block sees.  QuickJS unwinds to the call handler,
 * which raises the kept error in place of the exception; see
 * pljs_ereport_js_error_info().  Until then every exception pljs throws is
 * uncatchable as well, since C code can replace the pending exception with one
 * of its own, and a call that returns all the same raises the kept error; see
 * dispatch_call().
 *
 * @param ctx #JSContext - Javascript context
 * @returns #JSValue - JS_EXCEPTION
 */
JSValue pljs_throw_fatal_error(JSContext *ctx) {
  MemoryContext old_context;
  ErrorData *edata;

  /*
   * JavaScript only runs with storage installed, top-level code as its
   * function is compiled included; see pljs_compile_function().
   */
  Assert(current_storage != NULL);

  old_context =
      MemoryContextSwitchTo(current_storage->execution_memory_context);
  edata = CopyErrorData();

  FlushErrorState();
  MemoryContextSwitchTo(old_context);

  /* The first error is the one the call ends with. */
  if (current_storage->fatal_error == NULL) {
    current_storage->fatal_error = edata;
  } else {
    FreeErrorData(edata);
  }

  return js_throw_uncatchable(current_storage->fatal_error, ctx);
}

/*
 * Ends the running call with a copy of an error that has been caught and
 * flushed; see pljs_throw_fatal_error().  ReThrowError() puts the copy back
 * where pljs_throw_fatal_error() takes the error being handled from.
 */
JSValue pljs_throw_fatal_error_data(ErrorData *edata, JSContext *ctx) {
  MemoryContext old_context = CurrentMemoryContext;

  PG_TRY();
  {
    ReThrowError(edata);
  }
  PG_CATCH();
  {
    MemoryContextSwitchTo(old_context);

    return pljs_throw_fatal_error(ctx);
  }
  PG_END_TRY();

  pg_unreachable();
}

/**
 * @brief Raises the error the running call has to end with, if it has one.
 *
 * Before what JavaScript returned is converted.  JavaScript can run on after
 * the exception that was to end the call -- a Promise's executor turns it
 * into a rejection -- and return all the same, and an error converting what
 * it returned replaced the one the call had to end with: a timeout came back
 * as "returned row must be an object".
 */
static void pljs_raise_if_ending(void) {
  ErrorData *fatal_error = pljs_fatal_error();

  if (fatal_error != NULL) {
    ReThrowError(fatal_error);
  }
}

/**
 * @brief Whether the running call has to end with an error.
 *
 * Only an exception that is thrown cannot be caught, and JavaScript runs on
 * until one is: a Promise's executor turns the exception that was to end the
 * call into a rejection, and the code after it ran -- its pljs.execute(),
 * whose nextval() or advisory lock outlived the call that failed, and its
 * pljs.commit(), which committed that call's work.  So every builtin that
 * runs SQL refuses once the call has to end with an error, with
 * pljs_throw_ending().  See pljs_throw_fatal_error().
 *
 * @returns @c bool
 */
bool pljs_call_is_ending(void) { return pljs_fatal_error() != NULL; }

/**
 * @brief Throws the error the running call has to end with; see
 * pljs_call_is_ending().
 *
 * @param ctx #JSContext - Javascript context
 * @returns #JSValue - JS_EXCEPTION
 */
JSValue pljs_throw_ending(JSContext *ctx) {
  return js_throw_uncatchable(pljs_fatal_error(), ctx);
}

/*
 * Like js_throw(), but also attaches the Postgres error's detail, hint,
 * SQLSTATE (`code`, `sqlerrcode`, `sqlstate`), and extended diagnostic fields
 * (`schema_name`, `table_name`, `column_name`, `datatype_name`,
 * `constraint_name`) to the JS error object (matching plv8).  Used when a
 * Postgres error caught during SPI execution is surfaced to JavaScript, so the
 * full error envelope survives into JS and can be re-raised faithfully across a
 * nested pljs.execute() boundary instead of collapsing to the message alone.
 */
JSValue js_throw_error_data(ErrorData *edata, JSContext *ctx) {
  ErrorData *fatal_error = pljs_fatal_error();

  /*
   * Nothing JavaScript can catch, whatever the error: pljs.execute() or
   * return_next() that caught the kept error itself, raised on the way out of
   * a conversion; see pljs_throw_fatal_error().
   */
  if (fatal_error != NULL) {
    return js_throw_uncatchable(fatal_error, ctx);
  }

  /*
   * A cancel -- statement_timeout, pg_cancel_backend() -- ends the call.  By
   * the time it is raised it is no longer pending, and nothing interrupts
   * JavaScript that caught it again: a function that caught a timeout from
   * pljs.execute() and went on looping ran for ever.
   */
  if (edata->sqlerrcode == ERRCODE_QUERY_CANCELED && current_storage != NULL) {
    return pljs_throw_fatal_error_data(edata, ctx);
  }

  JSValue error = JS_NewError(ctx);

  JS_SetPropertyStr(ctx, error, "message",
                    js_error_string(ctx, edata->message));

  if (edata->detail) {
    JS_SetPropertyStr(ctx, error, "detail",
                      js_error_string(ctx, edata->detail));
  }

  if (edata->hint) {
    JS_SetPropertyStr(ctx, error, "hint", js_error_string(ctx, edata->hint));
  }

  if (edata->schema_name) {
    JS_SetPropertyStr(ctx, error, "schema_name",
                      js_error_string(ctx, edata->schema_name));
  }
  if (edata->table_name) {
    JS_SetPropertyStr(ctx, error, "table_name",
                      js_error_string(ctx, edata->table_name));
  }
  if (edata->column_name) {
    JS_SetPropertyStr(ctx, error, "column_name",
                      js_error_string(ctx, edata->column_name));
  }
  if (edata->datatype_name) {
    JS_SetPropertyStr(ctx, error, "datatype_name",
                      js_error_string(ctx, edata->datatype_name));
  }
  if (edata->constraint_name) {
    JS_SetPropertyStr(ctx, error, "constraint_name",
                      js_error_string(ctx, edata->constraint_name));
  }

  /*
   * Expose the SQLSTATE as both the packed integer (`code`) and the
   * five-character string (`sqlerrcode` and `sqlstate`) so callers written
   * against either plv8's `e.code` or pljs's `e.sqlstate`/`e.sqlerrcode` work
   * identically.
   */
  JS_SetPropertyStr(ctx, error, "code",
                    JS_NewInt32(ctx, edata->sqlerrcode));
  JS_SetPropertyStr(ctx, error, "sqlerrcode",
                    JS_NewString(ctx, unpack_sql_state(edata->sqlerrcode)));
  JS_SetPropertyStr(ctx, error, "sqlstate",
                    JS_NewString(ctx, unpack_sql_state(edata->sqlerrcode)));

  return JS_Throw(ctx, error);
}

/**
 * @brief Compiles a function pljs_find_js_function() found, in a
 * subtransaction.
 *
 * Compiling runs any code at the top level of the source, which can hold
 * anything -- a catalog pin, a relation lock -- when it raises, and only
 * rolling back releases it.  pljs.find_function() catches the error, and left
 * what it held, which COMMIT warned of.  Only compiling needs one: a function
 * already compiled is found without.  Where none can be begun, it compiles
 * without one, as it did before; see pljs_subxact_begin().
 *
 * @param context #pljs_context - the function
 * @returns #JSValue of the compiled function
 */
static JSValue pljs_compile_found_function(pljs_context *context) {
  pljs_subxact sx;
  JSValue func = JS_UNDEFINED;
  ErrorData *edata;

  pljs_subxact_init(&sx);

  PG_TRY();
  {
    pljs_subxact_begin(&sx, true);

    func = pljs_compile_function(context, false);
  }
  PG_CATCH();
  {
    ReThrowError(pljs_subxact_abort(&sx));
  }
  PG_END_TRY();

  edata = pljs_subxact_commit(&sx);

  if (edata != NULL) {
    JS_FreeValue(context->ctx, func);
    ReThrowError(edata);
  }

  return func;
}

/**
 * @brief Finds a `pljs` function and returns the JSValue of the function.
 *
 * Finds a function by its #Oid, compiles it in its own context, and
 * returns a #JSValue containing a compiled version of the function.
 * Note that no permissions checks are done, it is assumed these are
 * done before calling.
 *
 * @param fn_oid #Oid
 * @param ctx #JSContext - if NULL, the cached ctx will be used
 * @returns #JSValue representation of either the function if it exists
 * of `JS_UNDEFINED` if it does not
 */
JSValue pljs_find_js_function(Oid fn_oid, JSContext *ctx) {
  check_stack_depth();
  CHECK_FOR_INTERRUPTS();

  Form_pg_proc proc;
  Oid prolang;
  JSValue func = JS_UNDEFINED;

  HeapTuple functuple =
      SearchSysCache(PROCOID, ObjectIdGetDatum(fn_oid), 0, 0, 0);
  if (!HeapTupleIsValid(functuple)) { // NOLINT
    elog(ERROR, "cache lookup failed for function %u", fn_oid);
  }

  proc = (Form_pg_proc)GETSTRUCT(functuple);
  prolang = proc->prolang;
  Oid owner_id = proc->proowner;

  /* Should not happen? */
  if (!OidIsValid(prolang)) { // NOLINT
    ReleaseSysCache(functuple);
    return func;
  }

  pljs_context context = {0};

  pljs_function_cache_value *function_entry =
      ctx != NULL
          ? pljs_cache_function_find_by_ctx(ctx, fn_oid, functuple)
          : pljs_cache_function_find(GetUserId(), owner_id, fn_oid, functuple);

  if (function_entry != NULL) {
    pljs_function_cache_to_context(&context, function_entry);

    /*
     * Hand out a reference we own.  pljs_function_cache_to_context() borrows
     * the cache's, and the cache entry is that value's only owner -- but a
     * JSValue returned from a C function belongs to its caller, so
     * pljs.find_function() handed JavaScript a reference it had not counted.
     * The engine dropped it when the JS variable died, and after enough lookups
     * the refcount reached zero while the entry was still cached, leaving the
     * cache holding a freed object.  The next call through it terminated the
     * backend.
     */
    func = JS_DupValue(context.ctx, context.js_function);

    /*
     * The pin was previously released only on the cache-miss branch below, so a
     * pljs.find_function() that hit the cache -- the common case once a
     * function has been called once -- held a syscache pin on pg_proc for the
     * rest of the transaction.  Repeated lookups in one transaction accumulated
     * them, which is what produces "WARNING: resource was not closed: cache
     * pg_proc ... has count N" under USE_ASSERT_CHECKING.
     */
    ReleaseSysCache(functuple);
  } else {
    setup_function(NULL, functuple, &context);
    ReleaseSysCache(functuple);

    if (!pljs_is_js_language(prolang, NULL)) {
      return JS_UNDEFINED;
    }

    if (ctx == NULL) {
      context.ctx = pljs_get_context(GetUserId(), owner_id);
    } else {
      context.ctx = ctx;
    }

    func = pljs_compile_found_function(&context);
    if (!JS_IsFunction(context.ctx, func)) {
      JS_FreeValue(context.ctx, func);
      return JS_UNDEFINED;
    }

    context.js_function = func;
    pljs_context_cache_value *ce = pljs_cache_context_find_by_ctx(context.ctx);
    if (ce != NULL && ce->ctx == context.ctx) {
      pljs_cache_function_add(&context);
      func = JS_DupValue(context.ctx, func);
    }
  }

  // What is not a function is not found; see dispatch_call().
  if (!JS_IsFunction(context.ctx, func)) {
    JS_FreeValue(context.ctx, func);
    return JS_UNDEFINED;
  }

  return func;
}

/* ============================================================================
 * Table-Macro & Planner Support-Hook Subsystem
 * (pljs_source_in, pljs_source_out, pljs_call_support)
 * ============================================================================
 */

#define PLJS_NUM_INLINE_HELPERS 8
#define PLJS_MAX_INFERRED_CACHE 16
#define PLJS_MAX_HOOK_ENTRIES   32
#define PLJS_MAX_STAMPED_OIDS   64

typedef struct PljsInferredEntry {
  char *func_name;
  char *source_str;
  char *first_arg;
  int ncols;
  pljs_inferred_col *cols;
} PljsInferredEntry;

typedef struct PljsSupportHookEntry {
  bool in_use;
  char func_name[NAMEDATALEN];
  char infer_sql_func[NAMEDATALEN];
  char support_sql_func[NAMEDATALEN];
  JSContext *infer_ctx;
  JSValue infer_js_cb;
  JSContext *support_ctx;
  JSValue support_js_cb;
} PljsSupportHookEntry;

static PljsInferredEntry pljs_inferred_cache[PLJS_MAX_INFERRED_CACHE];
static int pljs_inferred_cache_next = 0;

static PljsSupportHookEntry pljs_hook_registry[PLJS_MAX_HOOK_ENTRIES];
static bool pljs_hook_registry_initialized = false;

static Oid pljs_stamped_oids[PLJS_MAX_STAMPED_OIDS];
static int pljs_num_stamped_oids = 0;

static bool pljs_in_support_internal_call = false;

static uint64 pljs_fnv1a64(uint64 h, const void *data, size_t len) {
  const unsigned char *p = (const unsigned char *)data;
  for (size_t i = 0; i < len; i++) {
    h ^= (uint64)p[i];
    h *= 1099511628211ULL;
  }
  return h;
}

static void pljs_ensure_hook_registry_init(void) {
  if (!pljs_hook_registry_initialized) {
    for (int i = 0; i < PLJS_MAX_HOOK_ENTRIES; i++) {
      pljs_hook_registry[i].in_use = false;
      pljs_hook_registry[i].func_name[0] = '\0';
      pljs_hook_registry[i].infer_sql_func[0] = '\0';
      pljs_hook_registry[i].support_sql_func[0] = '\0';
      pljs_hook_registry[i].infer_ctx = NULL;
      pljs_hook_registry[i].infer_js_cb = JS_UNDEFINED;
      pljs_hook_registry[i].support_ctx = NULL;
      pljs_hook_registry[i].support_js_cb = JS_UNDEFINED;
    }
    pljs_hook_registry_initialized = true;
  }
}

static void pljs_normalize_func_name(const char *raw, char *out, size_t out_sz) {
  if (raw == NULL || out_sz == 0) {
    if (out_sz > 0) {
      out[0] = '\0';
    }
    return;
  }

  const char *dot = strrchr(raw, '.');
  const char *p = dot ? (dot + 1) : raw;
  size_t idx = 0;

  while (*p != '\0' && idx + 1 < out_sz) {
    unsigned char c = (unsigned char)*p++;
    if (c == '"') {
      continue;
    }
    if (c >= 'A' && c <= 'Z') {
      c = (unsigned char)(c - 'A' + 'a');
    }
    out[idx++] = (char)c;
  }
  out[idx] = '\0';
}

static PljsSupportHookEntry *pljs_find_or_create_hook_entry(const char *func_name,
                                                            bool create) {
  pljs_ensure_hook_registry_init();
  char norm[NAMEDATALEN];
  pljs_normalize_func_name(func_name, norm, sizeof(norm));
  if (norm[0] == '\0') {
    return NULL;
  }

  int free_slot = -1;
  for (int i = 0; i < PLJS_MAX_HOOK_ENTRIES; i++) {
    if (pljs_hook_registry[i].in_use &&
        strcmp(pljs_hook_registry[i].func_name, norm) == 0) {
      return &pljs_hook_registry[i];
    }
    if (!pljs_hook_registry[i].in_use && free_slot < 0) {
      free_slot = i;
    }
  }

  if (!create || free_slot < 0) {
    return NULL;
  }

  PljsSupportHookEntry *e = &pljs_hook_registry[free_slot];
  e->in_use = true;
  strlcpy(e->func_name, norm, sizeof(e->func_name));
  e->infer_sql_func[0] = '\0';
  e->support_sql_func[0] = '\0';
  e->infer_ctx = NULL;
  e->infer_js_cb = JS_UNDEFINED;
  e->support_ctx = NULL;
  e->support_js_cb = JS_UNDEFINED;
  return e;
}

void pljs_support_free_context_callbacks(JSContext *ctx) {
  if (ctx == NULL || !pljs_hook_registry_initialized) {
    return;
  }

  for (int i = 0; i < PLJS_MAX_HOOK_ENTRIES; i++) {
    if (!pljs_hook_registry[i].in_use) {
      continue;
    }
    if (pljs_hook_registry[i].infer_ctx == ctx) {
      JS_FreeValue(ctx, pljs_hook_registry[i].infer_js_cb);
      pljs_hook_registry[i].infer_js_cb = JS_UNDEFINED;
      pljs_hook_registry[i].infer_ctx = NULL;
    }
    if (pljs_hook_registry[i].support_ctx == ctx) {
      JS_FreeValue(ctx, pljs_hook_registry[i].support_js_cb);
      pljs_hook_registry[i].support_js_cb = JS_UNDEFINED;
      pljs_hook_registry[i].support_ctx = NULL;
    }
  }
}

void pljs_register_col_inference_for_func(const char *func_name,
                                          const char *sql_func_name,
                                          JSContext *ctx, JSValueConst cb) {
  PljsSupportHookEntry *e = pljs_find_or_create_hook_entry(func_name, true);
  if (e == NULL) {
    return;
  }

  if (e->infer_ctx != NULL && !JS_IsUndefined(e->infer_js_cb)) {
    JS_FreeValue(e->infer_ctx, e->infer_js_cb);
  }
  e->infer_ctx = NULL;
  e->infer_js_cb = JS_UNDEFINED;
  e->infer_sql_func[0] = '\0';

  if (ctx != NULL && JS_IsFunction(ctx, cb)) {
    e->infer_ctx = ctx;
    e->infer_js_cb = JS_DupValue(ctx, cb);
  } else if (sql_func_name != NULL && sql_func_name[0] != '\0') {
    strlcpy(e->infer_sql_func, sql_func_name, sizeof(e->infer_sql_func));
  }
}

void pljs_register_support_for_func(const char *func_name,
                                    const char *sql_func_name, JSContext *ctx,
                                    JSValueConst cb) {
  PljsSupportHookEntry *e = pljs_find_or_create_hook_entry(func_name, true);
  if (e == NULL) {
    return;
  }

  if (e->support_ctx != NULL && !JS_IsUndefined(e->support_js_cb)) {
    JS_FreeValue(e->support_ctx, e->support_js_cb);
  }
  e->support_ctx = NULL;
  e->support_js_cb = JS_UNDEFINED;
  e->support_sql_func[0] = '\0';

  if (ctx != NULL && JS_IsFunction(ctx, cb)) {
    e->support_ctx = ctx;
    e->support_js_cb = JS_DupValue(ctx, cb);
  } else if (sql_func_name != NULL && sql_func_name[0] != '\0') {
    strlcpy(e->support_sql_func, sql_func_name, sizeof(e->support_sql_func));
  }
}

static void pljs_save_inferred_columns(const char *func_name,
                                       const char *source_str,
                                       const char *first_arg, int ncols,
                                       const pljs_inferred_col *cols) {
  if (ncols <= 0 || source_str == NULL) {
    return;
  }

  MemoryContext oldcxt = MemoryContextSwitchTo(TopMemoryContext);
  PljsInferredEntry *slot = &pljs_inferred_cache[pljs_inferred_cache_next];
  pljs_inferred_cache_next =
      (pljs_inferred_cache_next + 1) % PLJS_MAX_INFERRED_CACHE;

  if (slot->func_name != NULL) {
    pfree(slot->func_name);
  }
  if (slot->source_str != NULL) {
    pfree(slot->source_str);
  }
  if (slot->first_arg != NULL) {
    pfree(slot->first_arg);
  }
  if (slot->cols != NULL) {
    pfree(slot->cols);
  }

  slot->func_name = pstrdup(func_name ? func_name : "");
  slot->source_str = pstrdup(source_str);
  slot->first_arg = first_arg ? pstrdup(first_arg) : NULL;
  slot->ncols = ncols;
  slot->cols =
      (pljs_inferred_col *)palloc0(sizeof(pljs_inferred_col) * ncols);
  for (int i = 0; i < ncols; i++) {
    CHECK_FOR_INTERRUPTS();
    strlcpy(slot->cols[i].name,
            cols[i].name[0] ? cols[i].name : "?column?", NAMEDATALEN);
    slot->cols[i].type_oid = cols[i].type_oid;
    slot->cols[i].typmod = cols[i].typmod;
    slot->cols[i].collation_oid = cols[i].collation_oid;
  }

  MemoryContextSwitchTo(oldcxt);
}

static PljsInferredEntry *pljs_find_inferred_columns(const char *source_str) {
  if (source_str == NULL) {
    return NULL;
  }

  for (int i = 0; i < PLJS_MAX_INFERRED_CACHE; i++) {
    int idx = (pljs_inferred_cache_next - 1 - i + PLJS_MAX_INFERRED_CACHE) %
              PLJS_MAX_INFERRED_CACHE;

    CHECK_FOR_INTERRUPTS();
    if (pljs_inferred_cache[idx].source_str != NULL &&
        strcmp(pljs_inferred_cache[idx].source_str, source_str) == 0) {
      return &pljs_inferred_cache[idx];
    }
  }
  return NULL;
}

static Oid pljs_lookup_func_oid_by_name_nargs(const char *funcname, int nargs) {
  if (funcname == NULL || funcname[0] == '\0') {
    return InvalidOid;
  }

  Oid result = InvalidOid;
  CatCList *catlist =
      SearchSysCacheList1(PROCNAMEARGSNSP, CStringGetDatum(funcname));
  for (int i = 0; i < catlist->n_members; i++) {
    HeapTuple proctup = &catlist->members[i]->tuple;
    Form_pg_proc procform = (Form_pg_proc)GETSTRUCT(proctup);

    CHECK_FOR_INTERRUPTS();
    if (nargs < 0 || procform->pronargs == nargs) {
      result = procform->oid;
      break;
    }
  }
  ReleaseSysCacheList(catlist);
  return result;
}

static Oid pljs_find_infer_sql_func_oid(const char *func_name) {
  PljsSupportHookEntry *e = pljs_find_or_create_hook_entry(func_name, false);
  if (e != NULL && e->infer_sql_func[0] != '\0') {
    Oid oid = pljs_lookup_func_oid_by_name_nargs(e->infer_sql_func, 2);
    if (OidIsValid(oid)) {
      return oid;
    }
  }

  char candidate[NAMEDATALEN * 2];
  snprintf(candidate, sizeof(candidate), "%s_infer_columns",
           (func_name && func_name[0] != '\0') ? func_name : "graph_table");
  Oid oid = pljs_lookup_func_oid_by_name_nargs(candidate, 2);
  if (OidIsValid(oid)) {
    return oid;
  }

  if (func_name == NULL || func_name[0] == '\0' ||
      strcmp(func_name, "graph_table") == 0) {
    oid = pljs_lookup_func_oid_by_name_nargs("pgq_infer_columns_tsv", 2);
    if (OidIsValid(oid)) {
      return oid;
    }
  }

  return InvalidOid;
}

static Oid pljs_find_support_sql_func_oid(const char *func_name) {
  PljsSupportHookEntry *e = pljs_find_or_create_hook_entry(func_name, false);
  if (e != NULL && e->support_sql_func[0] != '\0') {
    Oid oid = pljs_lookup_func_oid_by_name_nargs(e->support_sql_func, 5);
    if (OidIsValid(oid)) {
      return oid;
    }
  }

  char candidate[NAMEDATALEN * 2];
  snprintf(candidate, sizeof(candidate), "%s_support",
           (func_name && func_name[0] != '\0') ? func_name : "graph_table");
  Oid oid = pljs_lookup_func_oid_by_name_nargs(candidate, 5);
  if (OidIsValid(oid)) {
    return oid;
  }

  if (func_name == NULL || func_name[0] == '\0' ||
      strcmp(func_name, "graph_table") == 0) {
    oid = pljs_lookup_func_oid_by_name_nargs("pgq_compile_graph_table_tsv", 5);
    if (OidIsValid(oid)) {
      return oid;
    }
  }

  return InvalidOid;
}

static Oid pljs_update_single_col_holder_type(const pljs_inferred_col *col) {
  static const char *holder_names[] = {
      "pljs_single_col_holder",
      "plv8_single_col_holder",
      "plpgq_single_col_holder",
      NULL,
  };
  Oid holder_type_oid = InvalidOid;
  Oid holder_relid = InvalidOid;

  if (col == NULL || XactReadOnly) {
    return InvalidOid;
  }

  for (int h = 0; holder_names[h] != NULL && !OidIsValid(holder_type_oid);
       h++) {
    CatCList *catlist =
        SearchSysCacheList1(TYPENAMENSP, CStringGetDatum(holder_names[h]));
    for (int i = 0; i < catlist->n_members; i++) {
      HeapTuple ttup = &catlist->members[i]->tuple;
      Form_pg_type tform = (Form_pg_type)GETSTRUCT(ttup);

      CHECK_FOR_INTERRUPTS();
      if (tform->typtype == TYPTYPE_COMPOSITE && OidIsValid(tform->typrelid)) {
        holder_type_oid = tform->oid;
        holder_relid = tform->typrelid;
        break;
      }
    }
    ReleaseSysCacheList(catlist);
  }

  if (!OidIsValid(holder_type_oid) || !OidIsValid(holder_relid)) {
    return InvalidOid;
  }

  pljs_cached_holder_relid = holder_relid;

  HeapTuple typtup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(col->type_oid));
  if (!HeapTupleIsValid(typtup)) {
    return InvalidOid;
  }
  Form_pg_type typform = (Form_pg_type)GETSTRUCT(typtup);
  int16 typlen = typform->typlen;
  bool typbyval = typform->typbyval;
  char typalign = typform->typalign;
  char typstorage = typform->typstorage;
  char typcategory = typform->typcategory;
  Oid typcollation = typform->typcollation;
  ReleaseSysCache(typtup);

  const char *desired_name = (col->name[0] != '\0') ? col->name : "?column?";
  Oid desired_coll =
      OidIsValid(col->collation_oid) ? col->collation_oid : typcollation;
  int16 desired_ndims = (typcategory == TYPCATEGORY_ARRAY) ? 1 : 0;

  HeapTuple cur_atttup = SearchSysCache2(ATTNUM, ObjectIdGetDatum(holder_relid),
                                         Int16GetDatum(1));
  if (HeapTupleIsValid(cur_atttup)) {
    Form_pg_attribute cur_att = (Form_pg_attribute)GETSTRUCT(cur_atttup);
    bool same =
        (strncmp(NameStr(cur_att->attname), desired_name, NAMEDATALEN - 1) ==
             0 &&
         cur_att->atttypid == col->type_oid &&
         cur_att->atttypmod == col->typmod &&
         cur_att->attcollation == desired_coll &&
         cur_att->attndims == desired_ndims);
    ReleaseSysCache(cur_atttup);
    if (same) {
      return holder_type_oid;
    }
  }

  Relation attrel = table_open(AttributeRelationId, ShareRowExclusiveLock);
  HeapTuple atttup = SearchSysCacheCopy2(ATTNUM, ObjectIdGetDatum(holder_relid),
                                         Int16GetDatum(1));
  if (!HeapTupleIsValid(atttup)) {
    table_close(attrel, NoLock);
    return InvalidOid;
  }

  Form_pg_attribute attform = (Form_pg_attribute)GETSTRUCT(atttup);
  if (strncmp(NameStr(attform->attname), desired_name, NAMEDATALEN - 1) == 0 &&
      attform->atttypid == col->type_oid &&
      attform->atttypmod == col->typmod &&
      attform->attcollation == desired_coll &&
      attform->attndims == desired_ndims) {
    heap_freetuple(atttup);
    table_close(attrel, NoLock);
    return holder_type_oid;
  }

  namestrcpy(&attform->attname, desired_name);
  attform->atttypid = col->type_oid;
  attform->attlen = typlen;
  attform->attbyval = typbyval;
  attform->attalign = typalign;
  attform->attstorage = typstorage;
#if PG_VERSION_NUM >= 140000
  attform->attcompression = '\0';
#endif
  attform->atttypmod = col->typmod;
  attform->attndims = desired_ndims;
  attform->attcollation = desired_coll;

  CatalogTupleUpdate(attrel, &atttup->t_self, atttup);
  heap_freetuple(atttup);
  table_close(attrel, NoLock);

  pljs_in_internal_catalog_update = true;
  CacheInvalidateRelcacheByRelid(holder_relid);
  pljs_in_internal_catalog_update = false;
  CommandCounterIncrement();

  return holder_type_oid;
}

static bool pljs_is_single_col_holder_type(Oid typid) {
  if (!OidIsValid(typid) || typid == RECORDOID) {
    return false;
  }

  HeapTuple typtup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(typid));
  if (!HeapTupleIsValid(typtup)) {
    return false;
  }
  Form_pg_type tform = (Form_pg_type)GETSTRUCT(typtup);
  bool match =
      (strcmp(NameStr(tform->typname), "pljs_single_col_holder") == 0 ||
       strcmp(NameStr(tform->typname), "plv8_single_col_holder") == 0 ||
       strcmp(NameStr(tform->typname), "plpgq_single_col_holder") == 0);
  ReleaseSysCache(typtup);
  return match;
}

static void pljs_record_stamped_oid(Oid funcid) {
  if (!OidIsValid(funcid)) {
    return;
  }
  for (int i = 0; i < pljs_num_stamped_oids; i++) {
    if (pljs_stamped_oids[i] == funcid) {
      return;
    }
  }
  if (pljs_num_stamped_oids < PLJS_MAX_STAMPED_OIDS) {
    pljs_stamped_oids[pljs_num_stamped_oids++] = funcid;
  }
}

static bool pljs_varlena_attr_equals(HeapTuple tup, TupleDesc tupdesc,
                                     int attnum, bool new_isnull,
                                     Datum new_val) {
  bool old_isnull = false;
  Datum old_val = heap_getattr(tup, attnum, tupdesc, &old_isnull);
  if (old_isnull != new_isnull) {
    return false;
  }
  if (new_isnull) {
    return true;
  }
  struct varlena *old_v = PG_DETOAST_DATUM_PACKED(old_val);
  struct varlena *new_v = PG_DETOAST_DATUM_PACKED(new_val);
  size_t old_len = VARSIZE_ANY_EXHDR(old_v);
  size_t new_len = VARSIZE_ANY_EXHDR(new_v);
  bool eq = (old_len == new_len &&
             memcmp(VARDATA_ANY(old_v), VARDATA_ANY(new_v), old_len) == 0);
  if ((Pointer)old_v != DatumGetPointer(old_val)) {
    pfree(old_v);
  }
  if ((Pointer)new_v != DatumGetPointer(new_val)) {
    pfree(new_v);
  }
  return eq;
}

void pljs_ensure_proc_support(Oid fn_oid) {
  if (!OidIsValid(fn_oid) || XactReadOnly) {
    return;
  }

  Oid support_oid = pljs_lookup_func_oid_by_name_nargs("pljs_call_support", 1);
  if (!OidIsValid(support_oid)) {
    support_oid = pljs_lookup_func_oid_by_name_nargs("plv8_call_support", 1);
  }
  if (!OidIsValid(support_oid)) {
    return;
  }

  HeapTuple check_tup = SearchSysCache1(PROCOID, ObjectIdGetDatum(fn_oid));
  if (!HeapTupleIsValid(check_tup)) {
    return;
  }
  Form_pg_proc check_form = (Form_pg_proc)GETSTRUCT(check_tup);
  bool needs_update =
      (check_form->proretset && !OidIsValid(check_form->prosupport));
  ReleaseSysCache(check_tup);

  if (!needs_update) {
    return;
  }

  Relation proc_rel = table_open(ProcedureRelationId, ShareRowExclusiveLock);
  HeapTuple tup = SearchSysCacheCopy1(PROCOID, ObjectIdGetDatum(fn_oid));
  if (!HeapTupleIsValid(tup)) {
    table_close(proc_rel, NoLock);
    return;
  }
  Form_pg_proc procform = (Form_pg_proc)GETSTRUCT(tup);
  if (!procform->proretset || OidIsValid(procform->prosupport)) {
    heap_freetuple(tup);
    table_close(proc_rel, NoLock);
    return;
  }

  TupleDesc proc_tupdesc = RelationGetDescr(proc_rel);
  Datum values[Natts_pg_proc];
  bool nulls[Natts_pg_proc];
  bool replaces[Natts_pg_proc];
  MemSet(values, 0, sizeof(values));
  MemSet(nulls, false, sizeof(nulls));
  MemSet(replaces, false, sizeof(replaces));

  values[Anum_pg_proc_prosupport - 1] = ObjectIdGetDatum(support_oid);
  replaces[Anum_pg_proc_prosupport - 1] = true;

  HeapTuple newtup =
      heap_modify_tuple(tup, proc_tupdesc, values, nulls, replaces);
  CatalogTupleUpdate(proc_rel, &newtup->t_self, newtup);
  pljs_cache_function_update_tuple_id(fn_oid, newtup);
  heap_freetuple(newtup);
  heap_freetuple(tup);
  table_close(proc_rel, NoLock);

  CommandCounterIncrement();
}

static void pljs_update_proc_table_columns(Oid funcid, int num_out_cols,
                                           const pljs_inferred_col *out_cols,
                                           const char *new_prosrc,
                                           int new_num_in_args,
                                           const Oid *new_in_arg_oids,
                                           Oid target_rettype) {
  if (!OidIsValid(funcid) || XactReadOnly) {
    return;
  }

  Relation proc_rel = table_open(ProcedureRelationId, ShareRowExclusiveLock);

  Oid single_holder_oid = InvalidOid;
  if (num_out_cols == 1 && out_cols != NULL && new_prosrc == NULL &&
      (!OidIsValid(target_rettype) ||
       pljs_is_single_col_holder_type(target_rettype))) {
    single_holder_oid = pljs_update_single_col_holder_type(&out_cols[0]);
  }

  HeapTuple tup = SearchSysCacheCopy1(PROCOID, ObjectIdGetDatum(funcid));
  if (!HeapTupleIsValid(tup)) {
    table_close(proc_rel, NoLock);
    return;
  }

  Form_pg_proc procform = (Form_pg_proc)GETSTRUCT(tup);
  TupleDesc proc_tupdesc = RelationGetDescr(proc_rel);

  if (num_out_cols <= 0 && new_prosrc == NULL && new_num_in_args < 0 &&
      procform->prorettype == RECORDOID &&
      heap_attisnull(tup, Anum_pg_proc_proallargtypes, proc_tupdesc)) {
    heap_freetuple(tup);
    table_close(proc_rel, NoLock);
    return;
  }

  Datum values[Natts_pg_proc];
  bool nulls[Natts_pg_proc];
  bool replaces[Natts_pg_proc];
  MemSet(values, 0, sizeof(values));
  MemSet(nulls, false, sizeof(nulls));
  MemSet(replaces, false, sizeof(replaces));

  int ninargs;
  const Oid *inargoids;

  if (new_num_in_args >= 0) {
    ninargs = new_num_in_args;
    inargoids = new_in_arg_oids;
    values[Anum_pg_proc_pronargs - 1] = Int16GetDatum((int16)ninargs);
    replaces[Anum_pg_proc_pronargs - 1] = true;
    values[Anum_pg_proc_proargtypes - 1] =
        PointerGetDatum(buildoidvector(inargoids, ninargs));
    replaces[Anum_pg_proc_proargtypes - 1] = true;
  } else {
    ninargs = procform->pronargs;
    inargoids = procform->proargtypes.values;
  }

  if (new_prosrc != NULL) {
    values[Anum_pg_proc_prosrc - 1] = CStringGetTextDatum(new_prosrc);
    replaces[Anum_pg_proc_prosrc - 1] = true;
  }

  Datum *existing_names = NULL;
  bool *existing_nulls = NULL;
  int n_existing_names = 0;
  if (new_num_in_args < 0 && ninargs > 0) {
    bool argnames_isnull = true;
    Datum argnames_datum = heap_getattr(tup, Anum_pg_proc_proargnames,
                                        proc_tupdesc,
                                        &argnames_isnull);
    if (!argnames_isnull) {
#if PG_VERSION_NUM >= 160000
      deconstruct_array_builtin(DatumGetArrayTypeP(argnames_datum), TEXTOID,
                                &existing_names, &existing_nulls,
                                &n_existing_names);
#else
      deconstruct_array(DatumGetArrayTypeP(argnames_datum), TEXTOID, -1, false,
                        TYPALIGN_INT, &existing_names, &existing_nulls,
                        &n_existing_names);
#endif
    }
  }

  bool has_real_in_argnames = false;
  if (existing_names != NULL && n_existing_names >= ninargs && ninargs > 0) {
    for (int i = 0; i < ninargs; i++) {
      if (!existing_nulls[i]) {
        char *nm = TextDatumGetCString(existing_names[i]);
        if (nm[0] != '\0' && strncmp(nm, "__in_", 5) != 0) {
          has_real_in_argnames = true;
        }
        pfree(nm);
        if (has_real_in_argnames) {
          break;
        }
      }
    }
  }

  if (num_out_cols <= 0) {
    Oid desired_rettype =
        OidIsValid(target_rettype) ? target_rettype : RECORDOID;
    values[Anum_pg_proc_prorettype - 1] = ObjectIdGetDatum(desired_rettype);
    replaces[Anum_pg_proc_prorettype - 1] = true;

    nulls[Anum_pg_proc_proallargtypes - 1] = true;
    replaces[Anum_pg_proc_proallargtypes - 1] = true;

    nulls[Anum_pg_proc_proargmodes - 1] = true;
    replaces[Anum_pg_proc_proargmodes - 1] = true;

    if (has_real_in_argnames) {
#if PG_VERSION_NUM >= 160000
      values[Anum_pg_proc_proargnames - 1] = PointerGetDatum(
          construct_array_builtin(existing_names, ninargs, TEXTOID));
#else
      values[Anum_pg_proc_proargnames - 1] =
          PointerGetDatum(construct_array(existing_names, ninargs, TEXTOID, -1,
                                          false, TYPALIGN_INT));
#endif
    } else {
      nulls[Anum_pg_proc_proargnames - 1] = true;
    }
    replaces[Anum_pg_proc_proargnames - 1] = true;
  } else if (num_out_cols == 1 && OidIsValid(single_holder_oid) &&
             new_prosrc == NULL &&
             (!OidIsValid(target_rettype) ||
              pljs_is_single_col_holder_type(target_rettype))) {
    values[Anum_pg_proc_prorettype - 1] = ObjectIdGetDatum(single_holder_oid);
    replaces[Anum_pg_proc_prorettype - 1] = true;

    nulls[Anum_pg_proc_proallargtypes - 1] = true;
    replaces[Anum_pg_proc_proallargtypes - 1] = true;

    nulls[Anum_pg_proc_proargmodes - 1] = true;
    replaces[Anum_pg_proc_proargmodes - 1] = true;

    if (has_real_in_argnames) {
#if PG_VERSION_NUM >= 160000
      values[Anum_pg_proc_proargnames - 1] = PointerGetDatum(
          construct_array_builtin(existing_names, ninargs, TEXTOID));
#else
      values[Anum_pg_proc_proargnames - 1] =
          PointerGetDatum(construct_array(existing_names, ninargs, TEXTOID, -1,
                                          false, TYPALIGN_INT));
#endif
    } else {
      nulls[Anum_pg_proc_proargnames - 1] = true;
    }
    replaces[Anum_pg_proc_proargnames - 1] = true;
  } else if (num_out_cols == 1 &&
             (new_prosrc != NULL ||
              (OidIsValid(target_rettype) && target_rettype != RECORDOID))) {
    int total_args = ninargs + 1;
    Datum *all_types = (Datum *)palloc(sizeof(Datum) * total_args);
    Datum *all_modes = (Datum *)palloc(sizeof(Datum) * total_args);
    Datum *all_names = (Datum *)palloc(sizeof(Datum) * total_args);
    Oid desired_rettype =
        (OidIsValid(target_rettype) && target_rettype != RECORDOID &&
         !pljs_is_single_col_holder_type(target_rettype))
            ? target_rettype
            : out_cols[0].type_oid;

    values[Anum_pg_proc_prorettype - 1] = ObjectIdGetDatum(desired_rettype);
    replaces[Anum_pg_proc_prorettype - 1] = true;

    for (int i = 0; i < ninargs; i++) {
      char argbuf[32];

      CHECK_FOR_INTERRUPTS();
      all_types[i] = ObjectIdGetDatum(inargoids[i]);
      all_modes[i] = CharGetDatum(PROARGMODE_IN);
      if (existing_names != NULL && i < n_existing_names &&
          !existing_nulls[i]) {
        all_names[i] = existing_names[i];
      } else {
        snprintf(argbuf, sizeof(argbuf), "__in_%d", i + 1);
        all_names[i] = CStringGetTextDatum(argbuf);
      }
    }
    all_types[ninargs] = ObjectIdGetDatum(out_cols[0].type_oid);
    all_modes[ninargs] = CharGetDatum(PROARGMODE_TABLE);
    all_names[ninargs] = CStringGetTextDatum(
        out_cols[0].name[0] ? out_cols[0].name : "?column?");

#if PG_VERSION_NUM >= 160000
    values[Anum_pg_proc_proallargtypes - 1] = PointerGetDatum(
        construct_array_builtin(all_types, total_args, OIDOID));
    replaces[Anum_pg_proc_proallargtypes - 1] = true;

    values[Anum_pg_proc_proargmodes - 1] = PointerGetDatum(
        construct_array_builtin(all_modes, total_args, CHAROID));
    replaces[Anum_pg_proc_proargmodes - 1] = true;

    values[Anum_pg_proc_proargnames - 1] = PointerGetDatum(
        construct_array_builtin(all_names, total_args, TEXTOID));
    replaces[Anum_pg_proc_proargnames - 1] = true;
#else
    values[Anum_pg_proc_proallargtypes - 1] =
        PointerGetDatum(construct_array(all_types, total_args, OIDOID,
                                        sizeof(Oid), true, TYPALIGN_INT));
    replaces[Anum_pg_proc_proallargtypes - 1] = true;

    values[Anum_pg_proc_proargmodes - 1] =
        PointerGetDatum(construct_array(all_modes, total_args, CHAROID, 1,
                                        true, TYPALIGN_CHAR));
    replaces[Anum_pg_proc_proargmodes - 1] = true;

    values[Anum_pg_proc_proargnames - 1] =
        PointerGetDatum(construct_array(all_names, total_args, TEXTOID, -1,
                                        false, TYPALIGN_INT));
    replaces[Anum_pg_proc_proargnames - 1] = true;
#endif
  } else {
    int total_args = ninargs + num_out_cols;
    Datum *all_types = (Datum *)palloc(sizeof(Datum) * total_args);
    Datum *all_modes = (Datum *)palloc(sizeof(Datum) * total_args);
    Datum *all_names = (Datum *)palloc(sizeof(Datum) * total_args);

    Oid desired_rettype =
        (OidIsValid(target_rettype) &&
         !pljs_is_single_col_holder_type(target_rettype))
            ? target_rettype
            : RECORDOID;
    values[Anum_pg_proc_prorettype - 1] = ObjectIdGetDatum(desired_rettype);
    replaces[Anum_pg_proc_prorettype - 1] = true;

    for (int i = 0; i < ninargs; i++) {
      char argbuf[32];

      CHECK_FOR_INTERRUPTS();
      all_types[i] = ObjectIdGetDatum(inargoids[i]);
      all_modes[i] = CharGetDatum(PROARGMODE_IN);
      if (existing_names != NULL && i < n_existing_names &&
          !existing_nulls[i]) {
        all_names[i] = existing_names[i];
      } else {
        snprintf(argbuf, sizeof(argbuf), "__in_%d", i + 1);
        all_names[i] = CStringGetTextDatum(argbuf);
      }
    }
    for (int i = 0; i < num_out_cols; i++) {
      CHECK_FOR_INTERRUPTS();
      all_types[ninargs + i] = ObjectIdGetDatum(out_cols[i].type_oid);
      all_modes[ninargs + i] = CharGetDatum(PROARGMODE_TABLE);
      all_names[ninargs + i] = CStringGetTextDatum(
          out_cols[i].name[0] ? out_cols[i].name : "?column?");
    }

#if PG_VERSION_NUM >= 160000
    values[Anum_pg_proc_proallargtypes - 1] = PointerGetDatum(
        construct_array_builtin(all_types, total_args, OIDOID));
    replaces[Anum_pg_proc_proallargtypes - 1] = true;

    values[Anum_pg_proc_proargmodes - 1] = PointerGetDatum(
        construct_array_builtin(all_modes, total_args, CHAROID));
    replaces[Anum_pg_proc_proargmodes - 1] = true;

    values[Anum_pg_proc_proargnames - 1] = PointerGetDatum(
        construct_array_builtin(all_names, total_args, TEXTOID));
    replaces[Anum_pg_proc_proargnames - 1] = true;
#else
    values[Anum_pg_proc_proallargtypes - 1] =
        PointerGetDatum(construct_array(all_types, total_args, OIDOID,
                                        sizeof(Oid), true, TYPALIGN_INT));
    replaces[Anum_pg_proc_proallargtypes - 1] = true;

    values[Anum_pg_proc_proargmodes - 1] =
        PointerGetDatum(construct_array(all_modes, total_args, CHAROID, 1,
                                        true, TYPALIGN_CHAR));
    replaces[Anum_pg_proc_proargmodes - 1] = true;

    values[Anum_pg_proc_proargnames - 1] =
        PointerGetDatum(construct_array(all_names, total_args, TEXTOID, -1,
                                        false, TYPALIGN_INT));
    replaces[Anum_pg_proc_proargnames - 1] = true;
#endif
  }

  bool already_matches = true;
  if (replaces[Anum_pg_proc_pronargs - 1]) {
    if (procform->pronargs != (int16)ninargs ||
        (ninargs > 0 &&
         memcmp(procform->proargtypes.values, inargoids,
                sizeof(Oid) * ninargs) != 0)) {
      already_matches = false;
    }
  }
  if (already_matches && replaces[Anum_pg_proc_prorettype - 1]) {
    if (procform->prorettype !=
        DatumGetObjectId(values[Anum_pg_proc_prorettype - 1])) {
      already_matches = false;
    }
  }
  if (already_matches && replaces[Anum_pg_proc_prosrc - 1]) {
    if (!pljs_varlena_attr_equals(tup, proc_tupdesc, Anum_pg_proc_prosrc,
                                  nulls[Anum_pg_proc_prosrc - 1],
                                  values[Anum_pg_proc_prosrc - 1])) {
      already_matches = false;
    }
  }
  if (already_matches && replaces[Anum_pg_proc_proallargtypes - 1]) {
    if (!pljs_varlena_attr_equals(tup, proc_tupdesc,
                                  Anum_pg_proc_proallargtypes,
                                  nulls[Anum_pg_proc_proallargtypes - 1],
                                  values[Anum_pg_proc_proallargtypes - 1])) {
      already_matches = false;
    }
  }
  if (already_matches && replaces[Anum_pg_proc_proargmodes - 1]) {
    if (!pljs_varlena_attr_equals(tup, proc_tupdesc, Anum_pg_proc_proargmodes,
                                  nulls[Anum_pg_proc_proargmodes - 1],
                                  values[Anum_pg_proc_proargmodes - 1])) {
      already_matches = false;
    }
  }
  if (already_matches && replaces[Anum_pg_proc_proargnames - 1]) {
    if (!pljs_varlena_attr_equals(tup, proc_tupdesc, Anum_pg_proc_proargnames,
                                  nulls[Anum_pg_proc_proargnames - 1],
                                  values[Anum_pg_proc_proargnames - 1])) {
      already_matches = false;
    }
  }

  if (already_matches) {
    heap_freetuple(tup);
    table_close(proc_rel, NoLock);
    if (num_out_cols > 0 && new_prosrc == NULL) {
      pljs_record_stamped_oid(funcid);
    }
    return;
  }

  HeapTuple newtup = heap_modify_tuple(tup, proc_tupdesc, values,
                                       nulls, replaces);
  CatalogTupleUpdate(proc_rel, &newtup->t_self, newtup);

  if (new_prosrc == NULL && new_num_in_args < 0) {
    pljs_cache_function_update_tuple_id(funcid, newtup);
  }

  heap_freetuple(newtup);
  heap_freetuple(tup);
  table_close(proc_rel, NoLock);

  CommandCounterIncrement();

  if (num_out_cols > 0 && new_prosrc == NULL) {
    pljs_record_stamped_oid(funcid);
  }
}

static int pljs_update_func_overloads_columns(const char *func_name,
                                              int num_out_cols,
                                              const pljs_inferred_col *out_cols) {
  if (XactReadOnly) {
    return 0;
  }

  char norm[NAMEDATALEN];
  pljs_normalize_func_name(func_name ? func_name : "graph_table", norm,
                           sizeof(norm));
  if (norm[0] == '\0') {
    strlcpy(norm, "graph_table", sizeof(norm));
  }

  List *oids = NIL;
  CatCList *catlist =
      SearchSysCacheList1(PROCNAMEARGSNSP, CStringGetDatum(norm));
  for (int i = 0; i < catlist->n_members; i++) {
    HeapTuple proctup = &catlist->members[i]->tuple;
    Form_pg_proc procform = (Form_pg_proc)GETSTRUCT(proctup);

    CHECK_FOR_INTERRUPTS();
    if (procform->proretset &&
        (procform->prorettype == RECORDOID ||
         pljs_is_single_col_holder_type(procform->prorettype))) {
      if (num_out_cols <= 0 && procform->prorettype == RECORDOID) {
        bool att_isnull = true;
        (void)SysCacheGetAttr(PROCOID, proctup, Anum_pg_proc_proallargtypes,
                              &att_isnull);
        if (att_isnull) {
          continue;
        }
      }
      oids = lappend_oid(oids, procform->oid);
    }
  }
  ReleaseSysCacheList(catlist);

  int count = 0;
  ListCell *lc;
  foreach (lc, oids) {
    Oid foid = lfirst_oid(lc);

    CHECK_FOR_INTERRUPTS();
    pljs_update_proc_table_columns(foid, num_out_cols, out_cols, NULL, -1,
                                   NULL, InvalidOid);
    if (num_out_cols > 0) {
      pljs_ensure_proc_support(foid);
    }
    count++;
  }
  list_free(oids);
  return count;
}

static void pljs_reset_all_stamped_procs(void) {
  if (pljs_in_support_internal_call || pljs_num_stamped_oids <= 0 ||
      XactReadOnly) {
    return;
  }

  int count = pljs_num_stamped_oids;
  Oid local_oids[PLJS_MAX_STAMPED_OIDS];
  for (int i = 0; i < count; i++) {
    local_oids[i] = pljs_stamped_oids[i];
  }
  pljs_num_stamped_oids = 0;

  MemoryContext saved_cxt = CurrentMemoryContext;
  PG_TRY();
  {
    for (int i = 0; i < count; i++) {
      CHECK_FOR_INTERRUPTS();
      pljs_update_proc_table_columns(local_oids[i], 0, NULL, NULL, -1, NULL,
                                     InvalidOid);
    }
  }
  PG_CATCH();
  {
    FlushErrorState();
    MemoryContextSwitchTo(saved_cxt);
  }
  PG_END_TRY();
}

int pljs_set_func_columns(const char *func_name, int ncols,
                          const pljs_inferred_col *cols) {
  return pljs_update_func_overloads_columns(func_name, ncols, cols);
}

static bool pljs_match_sql_literal_at(const char *p, const char *source_str,
                                      size_t src_len,
                                      const char **lit_end_out) {
  if (*p == '\'') {
    const char *q = p + 1;
    const char *s = source_str;

    while (*s != '\0') {
      if (*s == '\'') {
        if (q[0] == '\'' && q[1] == '\'') {
          q += 2;
          s++;
        } else if (q[0] == '\\' && q[1] == '\'') {
          q += 2;
          s++;
        } else {
          return false;
        }
      } else if (*q == *s) {
        q++;
        s++;
      } else {
        return false;
      }
    }

    if (*q == '\'' && q[1] != '\'') {
      *lit_end_out = q + 1;
      return true;
    }
    return false;
  }

  if (*p == '$') {
    const char *t = p + 1;
    while (isalnum((unsigned char)*t) || *t == '_') {
      t++;
    }
    if (*t == '$') {
      size_t tag_len = (size_t)(t - p) + 1;
      const char *body = t + 1;
      if (strncmp(body, source_str, src_len) == 0 &&
          strncmp(body + src_len, p, tag_len) == 0) {
        *lit_end_out = body + src_len + tag_len;
        return true;
      }
    }
  }

  return false;
}

static bool pljs_find_source_literal_from(const char *query_ctx,
                                          size_t start_offset,
                                          const char *source_str,
                                          size_t src_len,
                                          const char **quote_start_out,
                                          const char **lit_end_out) {
  const char *p = query_ctx + start_offset;

  while (*p != '\0') {
    CHECK_FOR_INTERRUPTS();

    if (p[0] == '-' && p[1] == '-') {
      p += 2;
      while (*p != '\0' && *p != '\n') {
        p++;
      }
      continue;
    }

    if (p[0] == '/' && p[1] == '*') {
      p += 2;
      while (*p != '\0' && !(p[0] == '*' && p[1] == '/')) {
        p++;
      }
      if (*p != '\0') {
        p += 2;
      }
      continue;
    }

    if (*p == '"') {
      p++;
      while (*p != '\0') {
        if (*p == '"') {
          if (p[1] == '"') {
            p += 2;
          } else {
            p++;
            break;
          }
        } else {
          p++;
        }
      }
      continue;
    }

    if (*p == '\'') {
      const char *lit_end = NULL;
      if (pljs_match_sql_literal_at(p, source_str, src_len, &lit_end)) {
        const char *qstart = p;
        if (qstart > query_ctx && (qstart[-1] == 'E' || qstart[-1] == 'e') &&
            (qstart - 1 == query_ctx ||
             (!isalnum((unsigned char)qstart[-2]) && qstart[-2] != '_'))) {
          qstart--;
        }
        *quote_start_out = qstart;
        *lit_end_out = lit_end;
        return true;
      }

      p++;
      while (*p != '\0') {
        if (*p == '\'' && p[1] == '\'') {
          p += 2;
        } else if (*p == '\\' && p[1] != '\0') {
          p += 2;
        } else if (*p == '\'') {
          p++;
          break;
        } else {
          p++;
        }
      }
      continue;
    }

    if (*p == '$') {
      const char *t = p + 1;
      while (isalnum((unsigned char)*t) || *t == '_') {
        t++;
      }
      if (*t == '$') {
        const char *lit_end = NULL;
        if (pljs_match_sql_literal_at(p, source_str, src_len, &lit_end)) {
          *quote_start_out = p;
          *lit_end_out = lit_end;
          return true;
        }

        size_t tag_len = (size_t)(t - p) + 1;
        const char *scan = t + 1;
        while (*scan != '\0') {
          if (*scan == '$' && strncmp(scan, p, tag_len) == 0) {
            scan += tag_len;
            break;
          }
          scan++;
        }
        p = scan;
        continue;
      }
    }

    p++;
  }

  return false;
}

static bool pljs_is_non_coldef_keyword(const char *tok_start, size_t tok_len) {
  static const char *const kw[] = {
      "AS",          "WHERE",   "JOIN",      "ON",        "USING",
      "ORDER",       "GROUP",   "HAVING",    "LIMIT",     "OFFSET",
      "FETCH",       "FOR",     "WINDOW",    "CROSS",     "LEFT",
      "RIGHT",       "FULL",    "INNER",     "OUTER",     "NATURAL",
      "LATERAL",     "UNION",   "INTERSECT", "EXCEPT",    "TABLESAMPLE",
      "RETURNING",   "INTO",    "VALUES",    "SELECT",    "FROM",
      NULL};
  for (int i = 0; kw[i] != NULL; i++) {
    if (strlen(kw[i]) == tok_len &&
        pg_strncasecmp(tok_start, kw[i], tok_len) == 0) {
      return true;
    }
  }
  return false;
}

static void pljs_extract_enclosing_call(const char *query_ctx,
                                        const char *source_str,
                                        char **func_name_out,
                                        char **first_arg_out,
                                        bool *has_coldeflist_out) {
  static const char *last_query_ctx = NULL;
  static size_t last_search_offset = 0;

  *func_name_out = pstrdup("graph_table");
  *first_arg_out = pstrdup("");
  *has_coldeflist_out = false;

  if (query_ctx == NULL || *query_ctx == '\0' || source_str == NULL ||
      *source_str == '\0') {
    return;
  }

  size_t query_len = strlen(query_ctx);
  size_t src_len = strlen(source_str);
  if (query_ctx != last_query_ctx || last_search_offset >= query_len) {
    last_query_ctx = query_ctx;
    last_search_offset = 0;
  }

  const char *quote_start = NULL;
  const char *lit_end = NULL;
  if (!pljs_find_source_literal_from(query_ctx, last_search_offset, source_str,
                                     src_len, &quote_start, &lit_end)) {
    if (last_search_offset == 0 ||
        !pljs_find_source_literal_from(query_ctx, 0, source_str, src_len,
                                       &quote_start, &lit_end)) {
      return;
    }
  }

  last_search_offset = (size_t)(lit_end - query_ctx);

  int depth = 0;
  bool in_squote_back = false;
  bool in_dquote_back = false;
  const char *open_paren = NULL;
  const char *first_comma_at_zero = NULL;

  for (const char *p = quote_start - 1; p >= query_ctx; p--) {
    char c = *p;
    CHECK_FOR_INTERRUPTS();
    if (in_squote_back) {
      if (c == '\'') {
        if (p > query_ctx && p[-1] == '\'') {
          p--;
        } else {
          in_squote_back = false;
        }
      }
      continue;
    }
    if (in_dquote_back) {
      if (c == '"') {
        if (p > query_ctx && p[-1] == '"') {
          p--;
        } else {
          in_dquote_back = false;
        }
      }
      continue;
    }
    if (c == '\'') {
      in_squote_back = true;
      continue;
    }
    if (c == '"') {
      in_dquote_back = true;
      continue;
    }
    if (c == ')') {
      depth++;
    } else if (c == '(') {
      if (depth == 0) {
        open_paren = p;
        break;
      }
      depth--;
    } else if (c == ',' && depth == 0) {
      first_comma_at_zero = p;
    }
  }

  if (open_paren != NULL) {
    const char *fn_end = open_paren;
    while (fn_end > query_ctx && isspace((unsigned char)fn_end[-1])) {
      fn_end--;
    }
    const char *fn_start = fn_end;
    while (fn_start > query_ctx &&
           (isalnum((unsigned char)fn_start[-1]) || fn_start[-1] == '_' ||
            fn_start[-1] == '.' || fn_start[-1] == '"')) {
      fn_start--;
    }
    if (fn_end > fn_start) {
      char *raw_fn = pnstrdup(fn_start, fn_end - fn_start);
      char norm[NAMEDATALEN];
      pljs_normalize_func_name(raw_fn, norm, sizeof(norm));
      pfree(raw_fn);
      if (norm[0] != '\0') {
        pfree(*func_name_out);
        *func_name_out = pstrdup(norm);
      }
    }

    if (first_comma_at_zero != NULL && first_comma_at_zero > open_paren + 1) {
      const char *a_start = open_paren + 1;
      const char *a_end = first_comma_at_zero;
      while (a_start < a_end && isspace((unsigned char)*a_start)) {
        a_start++;
      }
      while (a_end > a_start && isspace((unsigned char)a_end[-1])) {
        a_end--;
      }
      pfree(*first_arg_out);
      *first_arg_out = pnstrdup(a_start, a_end - a_start);
    }

    int fdepth = 1;
    bool in_squote = false;
    const char *close_paren = NULL;
    for (const char *p = lit_end; *p != '\0'; p++) {
      char c = *p;
      CHECK_FOR_INTERRUPTS();
      if (in_squote) {
        if (c == '\'') {
          if (p[1] == '\'') {
            p++;
          } else {
            in_squote = false;
          }
        }
        continue;
      }
      if (c == '\'') {
        in_squote = true;
        continue;
      }
      if (c == '(') {
        fdepth++;
      } else if (c == ')') {
        fdepth--;
        if (fdepth == 0) {
          close_paren = p;
          break;
        }
      }
    }

    if (close_paren != NULL) {
      const char *after = close_paren + 1;
      bool saw_as = false;
      while (*after != '\0' && isspace((unsigned char)*after)) {
        after++;
      }

      if (pg_strncasecmp(after, "AS", 2) == 0 &&
          (isspace((unsigned char)after[2]) || after[2] == '(')) {
        saw_as = true;
        after += 2;
        while (*after != '\0' && isspace((unsigned char)*after)) {
          after++;
        }
        if (*after == '(') {
          *has_coldeflist_out = true;
          return;
        }
      }

      if (isalpha((unsigned char)*after) || *after == '_' || *after == '"') {
        const char *tok_start = after;
        if (*after == '"') {
          after++;
          while (*after != '\0' && *after != '"') {
            after++;
          }
          if (*after == '"') {
            after++;
          }
        } else {
          while (isalnum((unsigned char)*after) || *after == '_') {
            after++;
          }
        }
        size_t tok_len = (size_t)(after - tok_start);
        if (saw_as || !pljs_is_non_coldef_keyword(tok_start, tok_len)) {
          while (*after != '\0' && isspace((unsigned char)*after)) {
            after++;
          }
          if (*after == '(') {
            *has_coldeflist_out = true;
          }
        }
      }
    }
  }
}

static void pljs_parse_and_apply_inferred_tsv(const char *func_name,
                                              const char *source_str,
                                              const char *fallback_first_arg,
                                              bool fallback_has_coldef,
                                              const char *tsv) {
  if (tsv == NULL || *tsv == '\0') {
    return;
  }

  bool has_coldef = fallback_has_coldef;
  char *first_arg = fallback_first_arg ? pstrdup(fallback_first_arg) : NULL;
  char *copy = pstrdup(tsv);
  char *saveptr = NULL;
  pljs_inferred_col cols[FUNC_MAX_ARGS];
  int ncols = 0;
  int line_idx = 0;

  for (char *line = strtok_r(copy, "\n", &saveptr); line != NULL;
       line = strtok_r(NULL, "\n", &saveptr)) {
    CHECK_FOR_INTERRUPTS();
    if (line_idx == 0 && strncmp(line, "COLDEF\t", 7) == 0) {
      if (strncmp(line, "COLDEF\t1", 8) == 0) {
        has_coldef = true;
      } else if (strncmp(line, "COLDEF\t0", 8) == 0) {
        has_coldef = false;
        if (line[8] == '\t' && line[9] != '\0') {
          first_arg = pstrdup(line + 9);
        }
      }
      line_idx++;
      continue;
    }
    if (ncols < FUNC_MAX_ARGS) {
      char *tab1 = strchr(line, '\t');
      if (tab1 != NULL) {
        *tab1 = '\0';
        char *tab2 = strchr(tab1 + 1, '\t');
        if (tab2 != NULL) {
          *tab2 = '\0';
          char *tab3 = strchr(tab2 + 1, '\t');
          if (tab3 != NULL) {
            *tab3 = '\0';
          }
          strlcpy(cols[ncols].name, line[0] ? line : "?column?", NAMEDATALEN);
          cols[ncols].type_oid = (Oid)atooid(tab1 + 1);
          cols[ncols].typmod = atoi(tab2 + 1);
          cols[ncols].collation_oid =
              tab3 ? (Oid)atooid(tab3 + 1) : InvalidOid;
          ncols++;
        }
      }
    }
    line_idx++;
  }

  if (ncols > 0) {
    pljs_save_inferred_columns(func_name, source_str, first_arg, ncols, cols);
  }

  if (has_coldef) {
    pljs_update_func_overloads_columns(func_name, 0, NULL);
  } else if (ncols > 0) {
    pljs_update_func_overloads_columns(func_name, ncols, cols);
  }
}

static int pljs_extract_cols_from_js_array(JSContext *ctx, JSValueConst arr,
                                           pljs_inferred_col *out_cols) {
  int32_t len = pljs_js_array_length(arr, ctx);
  if (len <= 0) {
    return 0;
  }
  if (len > FUNC_MAX_ARGS) {
    len = FUNC_MAX_ARGS;
  }
  int ncols = 0;

  for (int32_t i = 0; i < len; i++) {
    CHECK_FOR_INTERRUPTS();
    JSValue elem = JS_GetPropertyUint32(ctx, arr, (uint32_t)i);
    if (!JS_IsObject(elem) || JS_IsNull(elem)) {
      JS_FreeValue(ctx, elem);
      continue;
    }

    JSValue name_val = JS_GetPropertyStr(ctx, elem, "name");
    const char *cname =
        JS_IsString(name_val) ? JS_ToCString(ctx, name_val) : NULL;
    strlcpy(out_cols[ncols].name,
            (cname && cname[0]) ? cname : "?column?", NAMEDATALEN);
    if (cname) {
      JS_FreeCString(ctx, cname);
    }
    JS_FreeValue(ctx, name_val);

    Oid type_oid = InvalidOid;
    int32 typmod = -1;
    volatile Oid coll_oid = InvalidOid;

    JSValue oid_val = JS_GetPropertyStr(ctx, elem, "type_oid");
    uint32_t oid_num = 0;
    if (JS_IsNumber(oid_val) && JS_ToUint32(ctx, &oid_num, oid_val) == 0 &&
        oid_num != 0) {
      type_oid = (Oid)oid_num;
    }
    JS_FreeValue(ctx, oid_val);

    JSValue tm_val = JS_GetPropertyStr(ctx, elem, "typmod");
    int32_t tm_num = -1;
    if (JS_IsNumber(tm_val) && JS_ToInt32(ctx, &tm_num, tm_val) == 0) {
      typmod = tm_num;
    }
    JS_FreeValue(ctx, tm_val);

    JSValue coll_val = JS_GetPropertyStr(ctx, elem, "collation_oid");
    uint32_t coll_num = 0;
    if (JS_IsNumber(coll_val) && JS_ToUint32(ctx, &coll_num, coll_val) == 0) {
      coll_oid = (Oid)coll_num;
    }
    JS_FreeValue(ctx, coll_val);

    if (!OidIsValid(type_oid)) {
      JSValue tstr_val = JS_GetPropertyStr(ctx, elem, "type");
      if (!JS_IsString(tstr_val)) {
        JS_FreeValue(ctx, tstr_val);
        tstr_val = JS_GetPropertyStr(ctx, elem, "type_sql");
      }
      if (!JS_IsString(tstr_val)) {
        JS_FreeValue(ctx, tstr_val);
        tstr_val = JS_GetPropertyStr(ctx, elem, "type_name");
      }
      if (JS_IsString(tstr_val)) {
        const char *tstr = JS_ToCString(ctx, tstr_val);
        if (tstr != NULL) {
          MemoryContext saved_cxt = CurrentMemoryContext;
          PG_TRY();
          {
#if PG_VERSION_NUM >= 160000
            (void)parseTypeString(tstr, &type_oid, &typmod, NULL);
#else
            (void)parseTypeString(tstr, &type_oid, &typmod, false);
#endif
          }
          PG_CATCH();
          {
            FlushErrorState();
            MemoryContextSwitchTo(saved_cxt);
            type_oid = TEXTOID;
            typmod = -1;
          }
          PG_END_TRY();
          JS_FreeCString(ctx, tstr);
        }
      }
      JS_FreeValue(ctx, tstr_val);
    }

    JS_FreeValue(ctx, elem);

    if (!OidIsValid(type_oid)) {
      type_oid = TEXTOID;
    }

    out_cols[ncols].type_oid = type_oid;
    out_cols[ncols].typmod = typmod;
    out_cols[ncols].collation_oid = coll_oid;
    ncols++;
  }
  return ncols;
}

Datum pljs_source_in(PG_FUNCTION_ARGS) {
  char *str = PG_GETARG_CSTRING(0);
  const char *volatile query_ctx = debug_query_string ? debug_query_string : "";

  if (!pljs_in_support_internal_call && str != NULL && *str != '\0') {
    char *func_name = NULL;
    char *first_arg = NULL;
    bool has_coldeflist = false;

    pljs_extract_enclosing_call(query_ctx, str, &func_name, &first_arg,
                                &has_coldeflist);

    PljsSupportHookEntry *hook =
        pljs_find_or_create_hook_entry(func_name, false);
    if (hook != NULL && hook->infer_ctx != NULL &&
        JS_IsFunction(hook->infer_ctx, hook->infer_js_cb)) {
      char *inferred_tsv = NULL;
      pljs_inferred_col inferred_cols[FUNC_MAX_ARGS];
      int inferred_ncols = -1;

      JSContext *ctx = hook->infer_ctx;
      JSValue req = JS_NewObject(ctx);
      JS_SetPropertyStr(ctx, req, "func_name", JS_NewString(ctx, func_name));
      JS_SetPropertyStr(ctx, req, "query_string", JS_NewString(ctx, query_ctx));
      JS_SetPropertyStr(ctx, req, "source_arg", JS_NewString(ctx, str));
      JS_SetPropertyStr(ctx, req, "first_arg",
                        JS_NewString(ctx, first_arg ? first_arg : ""));
      JS_SetPropertyStr(ctx, req, "has_coldeflist",
                        JS_NewBool(ctx, has_coldeflist ? 1 : 0));

      JSValue res = JS_UNDEFINED;
      pljs_in_support_internal_call = true;
      bool ok = pljs_hook_call(ctx, hook->infer_js_cb, 1, &req, true, &res,
                               NULL);
      pljs_in_support_internal_call = false;
      JS_FreeValue(ctx, req);

      if (ok) {
        if (JS_IsString(res)) {
          const char *tsv_cs = JS_ToCString(ctx, res);
          if (tsv_cs != NULL) {
            inferred_tsv = pstrdup(tsv_cs);
            JS_FreeCString(ctx, tsv_cs);
          }
        } else if (JS_IsArray(ctx, res)) {
          inferred_ncols =
              pljs_extract_cols_from_js_array(ctx, res, inferred_cols);
        } else if (JS_IsObject(res) && !JS_IsNull(res)) {
          JSValue cd_val = JS_GetPropertyStr(ctx, res, "has_coldeflist");
          if (JS_IsBool(cd_val)) {
            has_coldeflist = JS_ToBool(ctx, cd_val) > 0;
          }
          JS_FreeValue(ctx, cd_val);

          JSValue fa_val = JS_GetPropertyStr(ctx, res, "first_arg");
          if (JS_IsString(fa_val)) {
            const char *facs = JS_ToCString(ctx, fa_val);
            if (facs != NULL) {
              first_arg = pstrdup(facs);
              JS_FreeCString(ctx, facs);
            }
          }
          JS_FreeValue(ctx, fa_val);

          JSValue cols_val = JS_GetPropertyStr(ctx, res, "columns");
          if (JS_IsArray(ctx, cols_val)) {
            inferred_ncols =
                pljs_extract_cols_from_js_array(ctx, cols_val, inferred_cols);
          }
          JS_FreeValue(ctx, cols_val);
        }
        JS_FreeValue(ctx, res);
      }

      if (inferred_tsv != NULL) {
        pljs_parse_and_apply_inferred_tsv(func_name, str, first_arg,
                                          has_coldeflist, inferred_tsv);
      } else if (inferred_ncols >= 0) {
        if (inferred_ncols > 0) {
          pljs_save_inferred_columns(func_name, str, first_arg, inferred_ncols,
                                     inferred_cols);
        }
        if (has_coldeflist) {
          pljs_update_func_overloads_columns(func_name, 0, NULL);
        } else if (inferred_ncols > 0) {
          pljs_update_func_overloads_columns(func_name, inferred_ncols,
                                             inferred_cols);
        }
      }
    } else {
      volatile Oid infer_oid = pljs_find_infer_sql_func_oid(func_name);
      if (OidIsValid(infer_oid)) {
        char *volatile tsv = NULL;
        pljs_in_support_internal_call = true;
        PG_TRY();
        {
          Datum res_datum =
              OidFunctionCall2(infer_oid, CStringGetTextDatum(query_ctx),
                               CStringGetTextDatum(str));
          tsv = TextDatumGetCString(res_datum);
        }
        PG_FINALLY();
        {
          pljs_in_support_internal_call = false;
        }
        PG_END_TRY();
        if (tsv != NULL) {
          pljs_parse_and_apply_inferred_tsv(func_name, str, first_arg,
                                            has_coldeflist, tsv);
        }
      }
    }
  }

  PG_RETURN_TEXT_P(cstring_to_text(str));
}

Datum pljs_source_out(PG_FUNCTION_ARGS) {
  Datum txt = PG_GETARG_DATUM(0);
  PG_RETURN_CSTRING(TextDatumGetCString(txt));
}

static char *pljs_extract_const_string(Node *node) {
  if (node == NULL) {
    return NULL;
  }
  while (IsA(node, RelabelType) || IsA(node, CoerceViaIO) ||
         IsA(node, CoerceToDomain)) {
    CHECK_FOR_INTERRUPTS();
    if (IsA(node, RelabelType)) {
      node = (Node *)((RelabelType *)node)->arg;
    } else if (IsA(node, CoerceViaIO)) {
      node = (Node *)((CoerceViaIO *)node)->arg;
    } else {
      node = (Node *)((CoerceToDomain *)node)->arg;
    }
  }
  if (IsA(node, Const)) {
    Const *c = (Const *)node;
    Oid typoutput;
    bool typIsVarlena;

    if (c->constisnull) {
      return NULL;
    }
    getTypeOutputInfo(c->consttype, &typoutput, &typIsVarlena);
    return OidOutputFunctionCall(typoutput, c->constvalue);
  }
  return NULL;
}

static bool pljs_is_source_type_node(Node *node) {
  if (node == NULL) {
    return false;
  }
  Oid typid = getBaseType(exprType(node));
  if (!OidIsValid(typid)) {
    return false;
  }
  HeapTuple tp = SearchSysCache1(TYPEOID, ObjectIdGetDatum(typid));
  if (!HeapTupleIsValid(tp)) {
    return false;
  }
  Form_pg_type tform = (Form_pg_type)GETSTRUCT(tp);
  bool match = (strcmp(NameStr(tform->typname), "pljs_source") == 0 ||
                strcmp(NameStr(tform->typname), "plv8_source") == 0 ||
                strcmp(NameStr(tform->typname), "pgq_pattern") == 0);
  ReleaseSysCache(tp);
  return match;
}

static bool pljs_is_null_const_node(Node *node) {
  while (node != NULL &&
         (IsA(node, RelabelType) || IsA(node, CoerceViaIO) ||
          IsA(node, CoerceToDomain))) {
    CHECK_FOR_INTERRUPTS();
    if (IsA(node, RelabelType)) {
      node = (Node *)((RelabelType *)node)->arg;
    } else if (IsA(node, CoerceViaIO)) {
      node = (Node *)((CoerceViaIO *)node)->arg;
    } else {
      node = (Node *)((CoerceToDomain *)node)->arg;
    }
  }
  return (node != NULL && IsA(node, Const) && ((Const *)node)->constisnull);
}

static char *pljs_extract_first_arg_string(Node *arg1) {
  char *const_str = pljs_extract_const_string(arg1);
  if (const_str != NULL) {
    return const_str;
  }

  while (arg1 != NULL &&
         (IsA(arg1, RelabelType) || IsA(arg1, CoerceViaIO) ||
          IsA(arg1, CoerceToDomain))) {
    CHECK_FOR_INTERRUPTS();
    if (IsA(arg1, RelabelType)) {
      arg1 = (Node *)((RelabelType *)arg1)->arg;
    } else if (IsA(arg1, CoerceViaIO)) {
      arg1 = (Node *)((CoerceViaIO *)arg1)->arg;
    } else {
      arg1 = (Node *)((CoerceToDomain *)arg1)->arg;
    }
  }

  if (arg1 != NULL && IsA(arg1, FuncExpr)) {
    FuncExpr *fe = (FuncExpr *)arg1;
    char *funcname = get_func_name(fe->funcid);
    Oid nspid = get_func_namespace(fe->funcid);
    char *nspname = OidIsValid(nspid) ? get_namespace_name(nspid) : NULL;

    if (funcname != NULL) {
      if (nspname != NULL) {
        return psprintf("%s.%s()", quote_identifier(nspname),
                        quote_identifier(funcname));
      }
      return psprintf("%s()", quote_identifier(funcname));
    }
  }

  return NULL;
}

static void pljs_append_json_string(StringInfo buf, const char *str) {
  appendStringInfoChar(buf, '"');
  if (str != NULL) {
    for (const unsigned char *p = (const unsigned char *)str; *p != '\0'; p++) {
      switch (*p) {
      case '"':
        appendStringInfoString(buf, "\\\"");
        break;
      case '\\':
        appendStringInfoString(buf, "\\\\");
        break;
      case '\b':
        appendStringInfoString(buf, "\\b");
        break;
      case '\f':
        appendStringInfoString(buf, "\\f");
        break;
      case '\n':
        appendStringInfoString(buf, "\\n");
        break;
      case '\r':
        appendStringInfoString(buf, "\\r");
        break;
      case '\t':
        appendStringInfoString(buf, "\\t");
        break;
      default:
        if (*p < 0x20) {
          appendStringInfo(buf, "\\u%04x", (int)*p);
        } else {
          appendStringInfoChar(buf, (char)*p);
        }
        break;
      }
    }
  }
  appendStringInfoChar(buf, '"');
}

static void pljs_append_rtable_to_lateral_json(StringInfo lat_buf, List *rtable,
                                               RangeTblEntry *skip_rte,
                                               int sublevels_up,
                                               bool *first_rte) {
  ListCell *lc;
  volatile int rtindex = 0;

  foreach (lc, rtable) {
    RangeTblEntry *rte = (RangeTblEntry *)lfirst(lc);
    List *colnames = NIL;
    List *colvars = NIL;
    ListCell *name_lc;
    ListCell *var_lc;
    volatile bool first_col = true;

    CHECK_FOR_INTERRUPTS();
    rtindex++;

    if (rte == skip_rte || rte->eref == NULL || rte->eref->aliasname == NULL) {
      continue;
    }
    if (rte->rtekind == RTE_SUBQUERY && rte->subquery == NULL) {
      continue;
    }
    if (rte->rtekind == RTE_JOIN &&
        (rte->joinaliasvars == NIL ||
         list_length(rte->eref->colnames) != list_length(rte->joinaliasvars))) {
      continue;
    }
    if (rte->rtekind == RTE_RESULT
#if PG_VERSION_NUM >= 180000
        || rte->rtekind == RTE_GROUP
#endif
    ) {
      continue;
    }

    if (rte->rtekind == RTE_FUNCTION) {
      bool can_expand = true;
      ListCell *flc;

      foreach (flc, rte->functions) {
        RangeTblFunction *rtfunc = (RangeTblFunction *)lfirst(flc);
        if (rtfunc->funccolnames == NIL) {
          Oid funcrettype = InvalidOid;
          TupleDesc tupdesc = NULL;
          TypeFuncClass functypclass =
              get_expr_result_type(rtfunc->funcexpr, &funcrettype, &tupdesc);

          if (functypclass == TYPEFUNC_COMPOSITE ||
              functypclass == TYPEFUNC_COMPOSITE_DOMAIN) {
            if (tupdesc == NULL || rtfunc->funccolcount > tupdesc->natts) {
              can_expand = false;
              break;
            }
          } else if (functypclass == TYPEFUNC_RECORD) {
            if (list_length(rtfunc->funccoltypes) != rtfunc->funccolcount) {
              can_expand = false;
              break;
            }
          } else if (functypclass != TYPEFUNC_SCALAR) {
            can_expand = false;
            break;
          }
        }
      }

      if (!can_expand) {
        if (list_length(rte->functions) == 1) {
          RangeTblFunction *rtfunc =
              (RangeTblFunction *)linitial(rte->functions);
          if (rtfunc->funcexpr != NULL && IsA(rtfunc->funcexpr, FuncExpr)) {
            FuncExpr *fe = (FuncExpr *)rtfunc->funcexpr;
            int fnargs = list_length(fe->args);
            if (fnargs >= 1) {
              bool src_first =
                  (fnargs == 1 ||
                   pljs_is_source_type_node((Node *)linitial(fe->args)));
              Node *snode = src_first
                                ? (Node *)linitial(fe->args)
                                : (fnargs >= 2 ? (Node *)lsecond(fe->args)
                                               : NULL);
              char *rsrc = pljs_extract_const_string(snode);
              PljsInferredEntry *inf = pljs_find_inferred_columns(rsrc);
              if (inf != NULL &&
                  inf->ncols == list_length(rte->eref->colnames)) {
                ListCell *clc;
                int cidx = 0;
                foreach (clc, rte->eref->colnames) {
                  const char *cn = strVal(lfirst(clc));
                  colnames = lappend(colnames, makeString(pstrdup(cn)));
                  colvars = lappend(colvars,
                                    makeVar(rtindex, cidx + 1,
                                            inf->cols[cidx].type_oid,
                                            inf->cols[cidx].typmod,
                                            inf->cols[cidx].collation_oid,
                                            sublevels_up));
                  cidx++;
                }
              }
            }
          }
        }
        if (colnames == NIL || colvars == NIL) {
          continue;
        }
      }
    }

    if (colnames == NIL || colvars == NIL) {
      MemoryContext saved_cxt = CurrentMemoryContext;
      PG_TRY();
      {
#if PG_VERSION_NUM >= 180000
        expandRTE(rte, rtindex, sublevels_up, VAR_RETURNING_DEFAULT, -1, false,
                  &colnames, &colvars);
#else
        expandRTE(rte, rtindex, sublevels_up, -1, false, &colnames, &colvars);
#endif
      }
      PG_CATCH();
      {
        FlushErrorState();
        MemoryContextSwitchTo(saved_cxt);
        colnames = NIL;
        colvars = NIL;
      }
      PG_END_TRY();
    }

    if (colnames == NIL || colvars == NIL) {
      continue;
    }

    if (!(*first_rte)) {
      appendStringInfoChar(lat_buf, ',');
    }
    *first_rte = false;

    appendStringInfoString(lat_buf, "{\"alias\":");
    pljs_append_json_string(lat_buf, rte->eref->aliasname);
    appendStringInfo(lat_buf, ",\"rtindex\":%d,\"columns\":[",
                     sublevels_up > 0 ? -rtindex : rtindex);

    forboth(name_lc, colnames, var_lc, colvars) {
      const char *colname = strVal(lfirst(name_lc));
      Node *varnode = (Node *)lfirst(var_lc);

      CHECK_FOR_INTERRUPTS();
      if (colname == NULL || *colname == '\0' || varnode == NULL ||
          !IsA(varnode, Var)) {
        continue;
      }

      Var *var = (Var *)varnode;
      if (!OidIsValid(var->vartype) || var->varattno <= 0) {
        continue;
      }

      if (!first_col) {
        appendStringInfoChar(lat_buf, ',');
      }
      first_col = false;

      appendStringInfoString(lat_buf, "{\"name\":");
      pljs_append_json_string(lat_buf, colname);
      appendStringInfo(
          lat_buf,
          ",\"attno\":%d,\"type_oid\":%u,\"typmod\":%d,\"collation_oid\":%u,"
          "\"type_sql\":",
          (int)var->varattno, var->vartype, var->vartypmod, var->varcollid);
      pljs_append_json_string(
          lat_buf, format_type_with_typemod(var->vartype, var->vartypmod));
      appendStringInfoChar(lat_buf, '}');
    }
    appendStringInfoString(lat_buf, "]}");
  }
}

static void pljs_materialize_rtfunc_for_rows_request(PlannerInfo *root,
                                                     FuncExpr *fexpr) {
  if (root == NULL || root->parse == NULL || fexpr == NULL) {
    return;
  }

  RangeTblFunction *target_rtfunc = NULL;
  ListCell *lc;
  foreach (lc, root->parse->rtable) {
    RangeTblEntry *rte = (RangeTblEntry *)lfirst(lc);

    CHECK_FOR_INTERRUPTS();
    if (rte->rtekind != RTE_FUNCTION) {
      continue;
    }
    ListCell *flc;
    foreach (flc, rte->functions) {
      RangeTblFunction *rtf = (RangeTblFunction *)lfirst(flc);

      CHECK_FOR_INTERRUPTS();
      if (rtf->funcexpr == (Node *)fexpr) {
        target_rtfunc = rtf;
        break;
      }
      if (target_rtfunc == NULL && rtf->funccolnames == NIL &&
          rtf->funcexpr != NULL && equal(rtf->funcexpr, (Node *)fexpr)) {
        target_rtfunc = rtf;
      }
    }
    if (target_rtfunc != NULL && target_rtfunc->funcexpr == (Node *)fexpr) {
      break;
    }
  }
  if (target_rtfunc == NULL) {
    return;
  }

  char *raw_func_name = get_func_name(fexpr->funcid);
  char func_name[NAMEDATALEN];
  pljs_normalize_func_name(raw_func_name ? raw_func_name : "graph_table",
                           func_name, sizeof(func_name));

  bool is_custom_lang = false;
  HeapTuple proctup =
      SearchSysCache1(PROCOID, ObjectIdGetDatum(fexpr->funcid));
  if (HeapTupleIsValid(proctup)) {
    Form_pg_proc procform = (Form_pg_proc)GETSTRUCT(proctup);
    Oid prolang = procform->prolang;
    ReleaseSysCache(proctup);
    HeapTuple langtup = SearchSysCache1(LANGOID, ObjectIdGetDatum(prolang));
    if (HeapTupleIsValid(langtup)) {
      Form_pg_language langform = (Form_pg_language)GETSTRUCT(langtup);
      char lang_name[NAMEDATALEN];
      pljs_normalize_func_name(NameStr(langform->lanname), lang_name,
                               sizeof(lang_name));
      is_custom_lang = (strcmp(lang_name, "pljs") != 0 &&
                        strcmp(lang_name, "sql") != 0 &&
                        strcmp(lang_name, "internal") != 0 &&
                        strcmp(lang_name, "c") != 0);
      ReleaseSysCache(langtup);
    }
  }
  if (is_custom_lang) {
    return;
  }

  if (target_rtfunc->funccolnames == NIL) {
    int nargs = list_length(fexpr->args);
    if (nargs >= 1) {
      bool source_is_first_arg =
          (nargs == 1 ||
           pljs_is_source_type_node((Node *)linitial(fexpr->args)));
      char *source_str =
          source_is_first_arg
              ? pljs_extract_const_string((Node *)linitial(fexpr->args))
              : (nargs >= 2
                     ? pljs_extract_const_string((Node *)lsecond(fexpr->args))
                     : NULL);
      if (source_str != NULL) {
        PljsInferredEntry *cached = pljs_find_inferred_columns(source_str);
        if (cached != NULL && cached->ncols > 0) {
          MemoryContext oldcxt =
              MemoryContextSwitchTo(GetMemoryChunkContext(target_rtfunc));
          List *colnames = NIL;
          List *coltypes = NIL;
          List *coltypmods = NIL;
          List *colcollations = NIL;

          for (int i = 0; i < cached->ncols; i++) {
            CHECK_FOR_INTERRUPTS();
            const char *cname =
                (cached->cols[i].name[0] != '\0') ? cached->cols[i].name
                                                  : "?column?";
            Oid ctype = OidIsValid(cached->cols[i].type_oid)
                            ? cached->cols[i].type_oid
                            : TEXTOID;
            int32 ctypmod = cached->cols[i].typmod;
            Oid ccoll = OidIsValid(cached->cols[i].collation_oid)
                            ? cached->cols[i].collation_oid
                            : get_typcollation(ctype);

            colnames = lappend(colnames, makeString(pstrdup(cname)));
            coltypes = lappend_oid(coltypes, ctype);
            coltypmods = lappend_int(coltypmods, ctypmod);
            colcollations = lappend_oid(colcollations, ccoll);
          }

          target_rtfunc->funccolnames = colnames;
          target_rtfunc->funccoltypes = coltypes;
          target_rtfunc->funccoltypmods = coltypmods;
          target_rtfunc->funccolcollations = colcollations;
          target_rtfunc->funccolcount = cached->ncols;
          MemoryContextSwitchTo(oldcxt);
        }
      }
    }
  }

  if (target_rtfunc->funccolnames != NIL) {
    if (fexpr->funcresulttype == RECORDOID ||
        pljs_is_single_col_holder_type(fexpr->funcresulttype)) {
      fexpr->funcresulttype = RECORDOID;
    }
    if (!root->parse->hasTargetSRFs) {
      pljs_update_func_overloads_columns(func_name, 0, NULL);
    }
  }
}

Datum pljs_call_support(PG_FUNCTION_ARGS) {
  Node *rawreq = (Node *)PG_GETARG_POINTER(0);

  if (rawreq == NULL) {
    PG_RETURN_POINTER(NULL);
  }

  if (IsA(rawreq, SupportRequestCost)) {
    SupportRequestCost *req = (SupportRequestCost *)rawreq;
    req->startup = 10.0;
    req->per_tuple = 0.01;
    PG_RETURN_POINTER(req);
  }

  if (IsA(rawreq, SupportRequestRows)) {
    SupportRequestRows *req = (SupportRequestRows *)rawreq;
    if (!pljs_in_support_internal_call && req->root != NULL &&
        req->root->parse != NULL && req->node != NULL &&
        IsA(req->node, FuncExpr)) {
      pljs_materialize_rtfunc_for_rows_request(req->root,
                                               (FuncExpr *)req->node);
    }
    req->rows = 100.0;
    PG_RETURN_POINTER(req);
  }

  if (IsA(rawreq, SupportRequestSimplify)) {
    SupportRequestSimplify *req = (SupportRequestSimplify *)rawreq;
    PlannerInfo *root = req->root;
    FuncExpr *fexpr = req->fcall;

    if (pljs_in_support_internal_call || root == NULL || root->parse == NULL ||
        fexpr == NULL) {
      PG_RETURN_POINTER(NULL);
    }

    char *raw_func_name = get_func_name(fexpr->funcid);
    char func_name[NAMEDATALEN];
    pljs_normalize_func_name(raw_func_name ? raw_func_name : "graph_table",
                             func_name, sizeof(func_name));

    char lang_name[NAMEDATALEN];
    lang_name[0] = '\0';
    bool is_custom_lang = false;
    {
      HeapTuple proctup =
          SearchSysCache1(PROCOID, ObjectIdGetDatum(fexpr->funcid));
      if (HeapTupleIsValid(proctup)) {
        Form_pg_proc procform = (Form_pg_proc)GETSTRUCT(proctup);
        Oid prolang = procform->prolang;
        Oid owner_id = procform->proowner;
        ReleaseSysCache(proctup);
        HeapTuple langtup = SearchSysCache1(LANGOID, ObjectIdGetDatum(prolang));
        if (HeapTupleIsValid(langtup)) {
          Form_pg_language langform = (Form_pg_language)GETSTRUCT(langtup);
          pljs_normalize_func_name(NameStr(langform->lanname), lang_name,
                                   sizeof(lang_name));
          is_custom_lang = (strcmp(lang_name, "pljs") != 0 &&
                            strcmp(lang_name, "sql") != 0 &&
                            strcmp(lang_name, "internal") != 0 &&
                            strcmp(lang_name, "c") != 0);
          ReleaseSysCache(langtup);
        }

        if (is_custom_lang) {
          PljsSupportHookEntry *lang_hook =
              pljs_find_or_create_hook_entry(lang_name, false);
          if (lang_hook == NULL || lang_hook->support_ctx == NULL ||
              !JS_IsFunction(lang_hook->support_ctx,
                             lang_hook->support_js_cb)) {
            pljs_in_support_internal_call = true;
            PG_TRY();
            {
              pljs_encoding_init();
              JSContext *ctx = pljs_get_context(GetUserId(), owner_id);
              JSValue fn_val = pljs_find_js_function(fexpr->funcid, ctx);
              JS_FreeValue(ctx, fn_val);
            }
            PG_CATCH();
            {
              FlushErrorState();
            }
            PG_END_TRY();
            pljs_in_support_internal_call = false;
          }
        }
      }
    }

    PljsSupportHookEntry *hook =
        pljs_find_or_create_hook_entry(func_name, false);
    if ((hook == NULL ||
         ((hook->support_ctx == NULL ||
           !JS_IsFunction(hook->support_ctx, hook->support_js_cb)) &&
          hook->support_sql_func[0] == '\0')) &&
        lang_name[0] != '\0') {
      PljsSupportHookEntry *lang_hook =
          pljs_find_or_create_hook_entry(lang_name, false);
      if (lang_hook != NULL &&
          ((lang_hook->support_ctx != NULL &&
            JS_IsFunction(lang_hook->support_ctx, lang_hook->support_js_cb)) ||
           lang_hook->support_sql_func[0] != '\0')) {
        hook = lang_hook;
      }
    }

    int nargs = list_length(fexpr->args);
    char *volatile first_arg_str = NULL;
    char *volatile source_str = NULL;
    char *volatile params_str = NULL;
    Node *params_arg_node = NULL;
    bool source_is_first_arg = true;

    if (!is_custom_lang) {
      if (nargs < 1) {
        PG_RETURN_POINTER(NULL);
      }
      source_is_first_arg =
          (nargs == 1 ||
           pljs_is_source_type_node((Node *)linitial(fexpr->args)));

      if (source_is_first_arg) {
        source_str = pljs_extract_const_string((Node *)linitial(fexpr->args));
        first_arg_str = pstrdup("");
        if (nargs >= 2) {
          params_arg_node = (Node *)lsecond(fexpr->args);
        }
      } else {
        source_str = pljs_extract_const_string((Node *)lsecond(fexpr->args));
        first_arg_str =
            pljs_extract_first_arg_string((Node *)linitial(fexpr->args));
        if (nargs >= 3) {
          params_arg_node = (Node *)lthird(fexpr->args);
        }
      }

      if (source_str == NULL) {
        PG_RETURN_POINTER(NULL);
      }
    } else {
      source_str = pstrdup("");
      first_arg_str = pstrdup("");
    }

    RangeTblEntry *volatile target_rte = NULL;
    RangeTblFunction *volatile target_rtfunc = NULL;
    RangeTblEntry *fallback_rte = NULL;
    RangeTblFunction *fallback_rtfunc = NULL;
    ListCell *lc;

    foreach (lc, root->parse->rtable) {
      RangeTblEntry *rte = (RangeTblEntry *)lfirst(lc);

      CHECK_FOR_INTERRUPTS();
      if (rte->rtekind == RTE_FUNCTION && list_length(rte->functions) == 1) {
        RangeTblFunction *rtfunc =
            (RangeTblFunction *)linitial(rte->functions);

        if (rtfunc->funcexpr != NULL && IsA(rtfunc->funcexpr, FuncExpr)) {
          FuncExpr *rte_fe = (FuncExpr *)rtfunc->funcexpr;

          if (rte_fe == fexpr) {
            target_rte = rte;
            target_rtfunc = rtfunc;
            break;
          }
          if (rte_fe->funcid == fexpr->funcid &&
              list_length(rte_fe->args) == nargs) {
            bool already_visited = (rte_fe->location == -2);
            bool exact_match = equal(rte_fe, fexpr);
            bool src_match = false;

            if (!exact_match && !is_custom_lang &&
                list_length(rte_fe->args) >= (source_is_first_arg ? 1 : 2)) {
              Node *src_node = source_is_first_arg
                                   ? (Node *)linitial(rte_fe->args)
                                   : (Node *)lsecond(rte_fe->args);
              char *rte_src = pljs_extract_const_string(src_node);

              if (rte_src != NULL && strcmp(rte_src, source_str) == 0) {
                src_match = true;
              }
            }

            if (exact_match || src_match || is_custom_lang) {
              if (!already_visited) {
                target_rte = rte;
                target_rtfunc = rtfunc;
                if (exact_match || src_match) {
                  break;
                }
              } else if (fallback_rte == NULL) {
                fallback_rte = rte;
                fallback_rtfunc = rtfunc;
              }
            }
          }
        }
      }
    }

    if (target_rte == NULL) {
      target_rte = fallback_rte;
      target_rtfunc = fallback_rtfunc;
    }

    if (target_rte == NULL) {
      PG_RETURN_POINTER(NULL);
    }

    if (target_rtfunc->funcexpr != NULL &&
        IsA(target_rtfunc->funcexpr, FuncExpr)) {
      ((FuncExpr *)target_rtfunc->funcexpr)->location = -2;
    }
    fexpr->location = -2;

    StringInfoData expected_cols_buf;
    initStringInfo(&expected_cols_buf);
    appendStringInfoChar(&expected_cols_buf, '[');

    int expected_ncols = 0;
    pljs_inferred_col expected_cols[FUNC_MAX_ARGS];

    if (target_rtfunc->funccolnames != NIL) {
      ListCell *cn_lc;
      ListCell *ct_lc;
      ListCell *cm_lc;
      ListCell *cc_lc;
      bool first = true;

      forfour(cn_lc, target_rtfunc->funccolnames, ct_lc,
              target_rtfunc->funccoltypes, cm_lc,
              target_rtfunc->funccoltypmods, cc_lc,
              target_rtfunc->funccolcollations) {
        const char *cname = strVal(lfirst(cn_lc));
        Oid ctype = lfirst_oid(ct_lc);
        int32 ctypmod = lfirst_int(cm_lc);
        Oid ccoll = lfirst_oid(cc_lc);

        CHECK_FOR_INTERRUPTS();
        if (!first) {
          appendStringInfoChar(&expected_cols_buf, ',');
        }
        first = false;

        appendStringInfoString(&expected_cols_buf, "{\"name\":");
        pljs_append_json_string(&expected_cols_buf, cname);
        appendStringInfo(&expected_cols_buf,
                         ",\"type_oid\":%u,\"typmod\":%d,\"collation_oid\":%u,"
                         "\"type_sql\":",
                         ctype, ctypmod, ccoll);
        pljs_append_json_string(&expected_cols_buf,
                                format_type_with_typemod(ctype, ctypmod));
        appendStringInfoChar(&expected_cols_buf, '}');

        if (expected_ncols < FUNC_MAX_ARGS) {
          strlcpy(expected_cols[expected_ncols].name,
                  cname ? cname : "?column?", NAMEDATALEN);
          expected_cols[expected_ncols].type_oid = ctype;
          expected_cols[expected_ncols].typmod = ctypmod;
          expected_cols[expected_ncols].collation_oid = ccoll;
          expected_ncols++;
        }
      }
    } else if (!is_custom_lang) {
      PljsInferredEntry *cached = pljs_find_inferred_columns(source_str);
      if (cached != NULL && cached->ncols > 0) {
        for (int i = 0; i < cached->ncols; i++) {
          CHECK_FOR_INTERRUPTS();
          if (i > 0) {
            appendStringInfoChar(&expected_cols_buf, ',');
          }
          appendStringInfoString(&expected_cols_buf, "{\"name\":");
          pljs_append_json_string(&expected_cols_buf, cached->cols[i].name);
          appendStringInfo(&expected_cols_buf,
                           ",\"type_oid\":%u,\"typmod\":%d,\"collation_oid\":"
                           "%u,\"type_sql\":",
                           cached->cols[i].type_oid, cached->cols[i].typmod,
                           cached->cols[i].collation_oid);
          pljs_append_json_string(
              &expected_cols_buf,
              format_type_with_typemod(cached->cols[i].type_oid,
                                       cached->cols[i].typmod));
          appendStringInfoChar(&expected_cols_buf, '}');

          if (expected_ncols < FUNC_MAX_ARGS) {
            expected_cols[expected_ncols++] = cached->cols[i];
          }
        }
      }
    }

    if (expected_ncols == 0) {
      Oid res_type_oid = InvalidOid;
      TupleDesc res_tupdesc = NULL;
      TypeFuncClass tfc =
          get_expr_result_type((Node *)fexpr, &res_type_oid, &res_tupdesc);
      if ((tfc == TYPEFUNC_COMPOSITE || tfc == TYPEFUNC_COMPOSITE_DOMAIN) &&
          res_tupdesc != NULL) {
        bool first = true;
        for (int i = 0; i < res_tupdesc->natts; i++) {
          Form_pg_attribute att = TupleDescAttr(res_tupdesc, i);
          if (att->attisdropped) {
            continue;
          }
          if (!first) {
            appendStringInfoChar(&expected_cols_buf, ',');
          }
          first = false;
          const char *cname = NameStr(att->attname);
          appendStringInfoString(&expected_cols_buf, "{\"name\":");
          pljs_append_json_string(&expected_cols_buf, cname);
          appendStringInfo(
              &expected_cols_buf,
              ",\"type_oid\":%u,\"typmod\":%d,\"collation_oid\":%u,"
              "\"type_sql\":",
              att->atttypid, att->atttypmod, att->attcollation);
          pljs_append_json_string(
              &expected_cols_buf,
              format_type_with_typemod(att->atttypid, att->atttypmod));
          appendStringInfoChar(&expected_cols_buf, '}');
          if (expected_ncols < FUNC_MAX_ARGS) {
            strlcpy(expected_cols[expected_ncols].name,
                    cname[0] ? cname : "?column?", NAMEDATALEN);
            expected_cols[expected_ncols].type_oid = att->atttypid;
            expected_cols[expected_ncols].typmod = att->atttypmod;
            expected_cols[expected_ncols].collation_oid = att->attcollation;
            expected_ncols++;
          }
        }
      } else if (tfc == TYPEFUNC_SCALAR && OidIsValid(res_type_oid)) {
        const char *cname =
            (target_rte->eref != NULL && target_rte->eref->colnames != NIL)
                ? strVal(linitial(target_rte->eref->colnames))
                : func_name;
        int32 ctypmod = exprTypmod((Node *)fexpr);
        Oid ccoll = exprCollation((Node *)fexpr);
        appendStringInfoString(&expected_cols_buf, "{\"name\":");
        pljs_append_json_string(&expected_cols_buf, cname);
        appendStringInfo(&expected_cols_buf,
                         ",\"type_oid\":%u,\"typmod\":%d,\"collation_oid\":%u,"
                         "\"type_sql\":",
                         res_type_oid, ctypmod, ccoll);
        pljs_append_json_string(&expected_cols_buf,
                                format_type_with_typemod(res_type_oid, ctypmod));
        appendStringInfoChar(&expected_cols_buf, '}');
        strlcpy(expected_cols[0].name,
                (cname && cname[0]) ? cname : "?column?", NAMEDATALEN);
        expected_cols[0].type_oid = res_type_oid;
        expected_cols[0].typmod = ctypmod;
        expected_cols[0].collation_oid = ccoll;
        expected_ncols = 1;
      }
    }
    appendStringInfoChar(&expected_cols_buf, ']');

    if (!is_custom_lang) {
      if (first_arg_str == NULL) {
        PljsInferredEntry *cached = pljs_find_inferred_columns(source_str);
        if (cached != NULL && cached->first_arg != NULL) {
          first_arg_str = pstrdup(cached->first_arg);
        }
      }
      if (first_arg_str == NULL) {
        if (target_rtfunc->funccolnames != NIL) {
          pljs_update_func_overloads_columns(func_name, 0, NULL);
        }
        PG_RETURN_POINTER(NULL);
      }

      if (params_arg_node != NULL && !pljs_is_null_const_node(params_arg_node)) {
        params_str = pljs_extract_const_string(params_arg_node);
        if (params_str == NULL) {
          if (target_rtfunc->funccolnames != NIL) {
            pljs_update_func_overloads_columns(func_name, 0, NULL);
          }
          PG_RETURN_POINTER(NULL);
        }
      }
    }

    StringInfoData lateral_env_buf;
    bool first_rte = true;
    initStringInfo(&lateral_env_buf);
    appendStringInfoChar(&lateral_env_buf, '[');
    pljs_append_rtable_to_lateral_json(&lateral_env_buf, root->parse->rtable,
                                       target_rte, 0, &first_rte);

    if (root->parent_root != NULL && root->parent_root->parse != NULL) {
      pljs_append_rtable_to_lateral_json(&lateral_env_buf,
                                         root->parent_root->parse->rtable, NULL,
                                         1, &first_rte);
    }
    appendStringInfoChar(&lateral_env_buf, ']');

    char *compiled_tsv = NULL;
    char *volatile sql_str = NULL;
    List *volatile lateral_args = NIL;
    Oid lateral_arg_oids[FUNC_MAX_ARGS];
    int nlateral = 0;
    volatile bool pass_call_args = false;

    if (hook != NULL && hook->support_ctx != NULL &&
        JS_IsFunction(hook->support_ctx, hook->support_js_cb)) {
      JSContext *ctx = hook->support_ctx;
      JSValue req_obj = JS_NewObject(ctx);
      JS_SetPropertyStr(ctx, req_obj, "request_type",
                        JS_NewString(ctx, "simplify"));
      JS_SetPropertyStr(ctx, req_obj, "func_oid",
                        JS_NewUint32(ctx, fexpr->funcid));
      JS_SetPropertyStr(ctx, req_obj, "func_name",
                        JS_NewString(ctx, func_name));
      JS_SetPropertyStr(ctx, req_obj, "lang_name",
                        JS_NewString(ctx, lang_name));
      JS_SetPropertyStr(ctx, req_obj, "nargs", JS_NewInt32(ctx, nargs));
      JS_SetPropertyStr(ctx, req_obj, "is_from_clause", JS_TRUE);
      JS_SetPropertyStr(
          ctx, req_obj, "has_coldeflist",
          JS_NewBool(ctx, target_rtfunc->funccolnames != NIL ? 1 : 0));
      JS_SetPropertyStr(ctx, req_obj, "first_arg",
                        JS_NewString(ctx, first_arg_str ? first_arg_str : ""));
      JS_SetPropertyStr(ctx, req_obj, "source_arg",
                        JS_NewString(ctx, source_str ? source_str : ""));

      JSValue call_args_arr = JS_NewArray(ctx);
      int arg_idx = 0;
      ListCell *alc;
      foreach (alc, fexpr->args) {
        Node *anode = (Node *)lfirst(alc);
        JSValue aobj = JS_NewObject(ctx);
        Oid atype = exprType(anode);
        int32 atypmod = exprTypmod(anode);
        Oid acoll = exprCollation(anode);
        bool is_null_c = pljs_is_null_const_node(anode);
        char *cval = is_null_c ? NULL : pljs_extract_const_string(anode);
        bool is_const = (is_null_c || cval != NULL);

        JS_SetPropertyStr(ctx, aobj, "index", JS_NewInt32(ctx, arg_idx + 1));
        JS_SetPropertyStr(ctx, aobj, "type_oid", JS_NewUint32(ctx, atype));
        JS_SetPropertyStr(ctx, aobj, "typmod", JS_NewInt32(ctx, atypmod));
        JS_SetPropertyStr(ctx, aobj, "collation_oid", JS_NewUint32(ctx, acoll));
        JS_SetPropertyStr(
            ctx, aobj, "type_sql",
            JS_NewString(ctx, format_type_with_typemod(atype, atypmod)));
        JS_SetPropertyStr(ctx, aobj, "is_const",
                          JS_NewBool(ctx, is_const ? 1 : 0));
        JS_SetPropertyStr(ctx, aobj, "is_null",
                          JS_NewBool(ctx, is_null_c ? 1 : 0));
        if (cval != NULL) {
          JS_SetPropertyStr(ctx, aobj, "const_val", JS_NewString(ctx, cval));
        } else {
          JS_SetPropertyStr(ctx, aobj, "const_val", JS_NULL);
        }
        JS_SetPropertyUint32(ctx, call_args_arr, (uint32_t)arg_idx, aobj);
        arg_idx++;
      }
      JS_SetPropertyStr(ctx, req_obj, "call_args", call_args_arr);

      if (params_str != NULL) {
        JSValue pval =
            JS_ParseJSON(ctx, params_str, strlen(params_str), "<params>");
        if (JS_IsException(pval)) {
          JS_FreeValue(ctx, JS_GetException(ctx));
          pval = JS_NULL;
        }
        JS_SetPropertyStr(ctx, req_obj, "params", pval);
      } else {
        JS_SetPropertyStr(ctx, req_obj, "params", JS_NULL);
      }
      JSValue exp_cols_val = JS_ParseJSON(
          ctx, expected_cols_buf.data, expected_cols_buf.len, "<expected_cols>");
      if (JS_IsException(exp_cols_val)) {
        JS_FreeValue(ctx, JS_GetException(ctx));
        exp_cols_val = JS_NewArray(ctx);
      }
      JS_SetPropertyStr(ctx, req_obj, "expected_columns", exp_cols_val);

      JSValue lat_env_val = JS_ParseJSON(
          ctx, lateral_env_buf.data, lateral_env_buf.len, "<lateral_env>");
      if (JS_IsException(lat_env_val)) {
        JS_FreeValue(ctx, JS_GetException(ctx));
        lat_env_val = JS_NewArray(ctx);
      }
      JS_SetPropertyStr(ctx, req_obj, "lateral_env", lat_env_val);

      JSValue res = JS_UNDEFINED;
      char *hook_err = NULL;
      pljs_in_support_internal_call = true;
      bool ok = pljs_hook_call(ctx, hook->support_js_cb, 1, &req_obj, true,
                               &res, &hook_err);
      pljs_in_support_internal_call = false;
      JS_FreeValue(ctx, req_obj);

      if (!ok) {
        ereport(ERROR,
                (errcode(ERRCODE_INTERNAL_ERROR),
                 errmsg("%s", hook_err ? hook_err
                                       : "planner support callback failed")));
      }

      {
        if (JS_IsString(res)) {
          const char *cs = JS_ToCString(ctx, res);
          if (cs != NULL) {
            compiled_tsv = pstrdup(cs);
            JS_FreeCString(ctx, cs);
          }
        } else if (JS_IsObject(res) && !JS_IsNull(res)) {
          JSValue sql_val = JS_GetPropertyStr(ctx, res, "sql");
          if (JS_IsString(sql_val)) {
            const char *scs = JS_ToCString(ctx, sql_val);
            if (scs != NULL) {
              sql_str = pstrdup(scs);
              JS_FreeCString(ctx, scs);
            }
          }
          JS_FreeValue(ctx, sql_val);

          JSValue pca_val = JS_GetPropertyStr(ctx, res, "pass_call_args");
          if (JS_IsBool(pca_val) && JS_ToBool(ctx, pca_val) > 0) {
            pass_call_args = true;
          }
          JS_FreeValue(ctx, pca_val);

          JSValue cols_val = JS_GetPropertyStr(ctx, res, "columns");
          if (JS_IsArray(ctx, cols_val)) {
            pljs_inferred_col ccols[FUNC_MAX_ARGS];
            int nccols = pljs_extract_cols_from_js_array(ctx, cols_val, ccols);
            if (expected_ncols == 0 && nccols > 0) {
              for (int i = 0; i < nccols; i++) {
                expected_cols[i] = ccols[i];
              }
              expected_ncols = nccols;
            }
          }
          JS_FreeValue(ctx, cols_val);

          JSValue lvars_val = JS_GetPropertyStr(ctx, res, "lateral_vars");
          if (JS_IsArray(ctx, lvars_val)) {
            int32_t llen = pljs_js_array_length(lvars_val, ctx);
            for (int32_t i = 0; i < llen && nlateral < FUNC_MAX_ARGS; i++) {
              JSValue lelem =
                  JS_GetPropertyUint32(ctx, lvars_val, (uint32_t)i);
              if (!JS_IsObject(lelem) || JS_IsNull(lelem)) {
                JS_FreeValue(ctx, lelem);
                continue;
              }
              int32_t raw_rtindex = 0;
              int varlevelsup = 0;
              int32_t attno_i = 0;
              uint32_t vtype_u = 0;
              int32_t vtypmod = -1;
              uint32_t vcoll_u = 0;

              JSValue v = JS_GetPropertyStr(ctx, lelem, "rtindex");
              if (JS_IsNumber(v)) {
                (void)JS_ToInt32(ctx, &raw_rtindex, v);
              }
              JS_FreeValue(ctx, v);
              if (raw_rtindex < 0) {
                raw_rtindex = -raw_rtindex;
                varlevelsup = 1;
              }

              v = JS_GetPropertyStr(ctx, lelem, "attno");
              if (JS_IsNumber(v)) {
                (void)JS_ToInt32(ctx, &attno_i, v);
              }
              JS_FreeValue(ctx, v);

              v = JS_GetPropertyStr(ctx, lelem, "type_oid");
              if (JS_IsNumber(v)) {
                (void)JS_ToUint32(ctx, &vtype_u, v);
              }
              JS_FreeValue(ctx, v);

              v = JS_GetPropertyStr(ctx, lelem, "typmod");
              if (JS_IsNumber(v)) {
                (void)JS_ToInt32(ctx, &vtypmod, v);
              }
              JS_FreeValue(ctx, v);

              v = JS_GetPropertyStr(ctx, lelem, "collation_oid");
              if (JS_IsNumber(v)) {
                (void)JS_ToUint32(ctx, &vcoll_u, v);
              }
              JS_FreeValue(ctx, v);
              JS_FreeValue(ctx, lelem);

              if (raw_rtindex > 0 && attno_i > 0 && OidIsValid((Oid)vtype_u)) {
                Var *vnode =
                    makeVar((Index)raw_rtindex, (AttrNumber)attno_i,
                            (Oid)vtype_u, vtypmod, (Oid)vcoll_u,
                            (Index)varlevelsup);
                lateral_args = lappend(lateral_args, vnode);
                lateral_arg_oids[nlateral++] = (Oid)vtype_u;
              }
            }
          }
          JS_FreeValue(ctx, lvars_val);
        }
        JS_FreeValue(ctx, res);
      }
    } else {
      Oid compile_oid = pljs_find_support_sql_func_oid(func_name);
      if (!OidIsValid(compile_oid) && lang_name[0] != '\0') {
        compile_oid = pljs_find_support_sql_func_oid(lang_name);
      }
      if (!OidIsValid(compile_oid)) {
        if (!is_custom_lang && target_rtfunc->funccolnames != NIL) {
          pljs_update_func_overloads_columns(func_name, 0, NULL);
        }
        PG_RETURN_POINTER(NULL);
      }

      pljs_in_support_internal_call = true;
      PG_TRY();
      {
        Datum compiled_datum = OidFunctionCall5(
            compile_oid, CStringGetTextDatum(first_arg_str),
            CStringGetTextDatum(source_str),
            CStringGetTextDatum(expected_cols_buf.data),
            CStringGetTextDatum(lateral_env_buf.data),
            CStringGetTextDatum(params_str ? params_str : ""));
        compiled_tsv = TextDatumGetCString(compiled_datum);
      }
      PG_FINALLY();
      {
        pljs_in_support_internal_call = false;
      }
      PG_END_TRY();
    }

    if (compiled_tsv != NULL) {
      char *copy = pstrdup(compiled_tsv);
      char *saveptr = NULL;
      int line_idx = 0;
      pljs_inferred_col compiled_cols[FUNC_MAX_ARGS];
      int ncompiled_cols = 0;

      for (char *line = strtok_r(copy, "\n", &saveptr); line != NULL;
           line = strtok_r(NULL, "\n", &saveptr)) {
        CHECK_FOR_INTERRUPTS();
        if (line_idx == 0 && strncmp(line, "SQL\t", 4) == 0) {
          sql_str = pstrdup(line + 4);
          line_idx++;
          continue;
        }
        if (strcmp(line, "PASS_CALL_ARGS\t1") == 0) {
          pass_call_args = true;
        } else if (strncmp(line, "COL\t", 4) == 0 &&
                   ncompiled_cols < FUNC_MAX_ARGS) {
          char *p1 = line + 4;
          char *t1 = strchr(p1, '\t');
          if (t1 != NULL) {
            *t1 = '\0';
            char *t2 = strchr(t1 + 1, '\t');
            if (t2 != NULL) {
              *t2 = '\0';
              char *t3 = strchr(t2 + 1, '\t');
              if (t3 != NULL) {
                *t3 = '\0';
              }
              strlcpy(compiled_cols[ncompiled_cols].name,
                      p1[0] ? p1 : "?column?", NAMEDATALEN);
              compiled_cols[ncompiled_cols].type_oid = (Oid)atooid(t1 + 1);
              compiled_cols[ncompiled_cols].typmod = atoi(t2 + 1);
              compiled_cols[ncompiled_cols].collation_oid =
                  t3 ? (Oid)atooid(t3 + 1) : InvalidOid;
              ncompiled_cols++;
            }
          }
        } else if (strncmp(line, "LAT\t", 4) == 0 && nlateral < FUNC_MAX_ARGS) {
          char *p1 = line + 4;
          char *t1 = strchr(p1, '\t');
          if (t1 != NULL) {
            *t1 = '\0';
            char *t2 = strchr(t1 + 1, '\t');
            if (t2 != NULL) {
              *t2 = '\0';
              char *t3 = strchr(t2 + 1, '\t');
              if (t3 != NULL) {
                *t3 = '\0';
                char *t4 = strchr(t3 + 1, '\t');
                if (t4 != NULL) {
                  *t4 = '\0';
                }

                int raw_rtindex = atoi(p1);
                int varlevelsup = 0;
                if (raw_rtindex < 0) {
                  raw_rtindex = -raw_rtindex;
                  varlevelsup = 1;
                }
                AttrNumber attno = (AttrNumber)atoi(t1 + 1);
                Oid vtype = (Oid)atooid(t2 + 1);
                int32 vtypmod = atoi(t3 + 1);
                Oid vcoll = t4 ? (Oid)atooid(t4 + 1) : InvalidOid;

                Var *vnode = makeVar((Index)raw_rtindex, attno, vtype, vtypmod,
                                     vcoll, (Index)varlevelsup);
                lateral_args = lappend(lateral_args, vnode);
                lateral_arg_oids[nlateral++] = vtype;
              }
            }
          }
        }
        line_idx++;
      }

      if (expected_ncols == 0 && ncompiled_cols > 0) {
        for (int i = 0; i < ncompiled_cols; i++) {
          expected_cols[i] = compiled_cols[i];
        }
        expected_ncols = ncompiled_cols;
      }
    }

    if (sql_str == NULL || *sql_str == '\0') {
      if (!is_custom_lang && target_rtfunc->funccolnames != NIL) {
        pljs_update_func_overloads_columns(func_name, 0, NULL);
      }
      PG_RETURN_POINTER(NULL);
    }

    if (!is_custom_lang) {
      pljs_update_func_overloads_columns(func_name, 0, NULL);
    }

    List *helper_args = NIL;
    Oid helper_arg_oids[FUNC_MAX_ARGS];
    int n_helper_args = 0;
    bool has_nonconst_arg = (nlateral > 0);

    if (pass_call_args) {
      ListCell *alc;
      foreach (alc, fexpr->args) {
        Node *anode = (Node *)lfirst(alc);
        if (n_helper_args >= FUNC_MAX_ARGS) {
          break;
        }
        helper_args = lappend(helper_args, copyObjectImpl(anode));
        helper_arg_oids[n_helper_args++] = exprType(anode);
        if (!IsA(anode, Const)) {
          has_nonconst_arg = true;
        }
      }
    }
    if (nlateral > 0) {
      ListCell *llc;
      int lidx = 0;
      foreach (llc, lateral_args) {
        if (n_helper_args >= FUNC_MAX_ARGS) {
          break;
        }
        helper_args = lappend(helper_args, lfirst(llc));
        helper_arg_oids[n_helper_args++] = lateral_arg_oids[lidx++];
      }
    }

    int helper_ncols = target_rtfunc->funccolnames != NIL ? 0 : expected_ncols;
    Oid target_rettype = fexpr->funcresulttype;
    if (OidIsValid(target_rettype) && target_rettype != RECORDOID &&
        !pljs_is_single_col_holder_type(target_rettype) && helper_ncols > 0) {
      HeapTuple rttup = SearchSysCache1(TYPEOID, ObjectIdGetDatum(target_rettype));
      if (HeapTupleIsValid(rttup)) {
        Form_pg_type rtform = (Form_pg_type)GETSTRUCT(rttup);
        if (rtform->typtype == TYPTYPE_COMPOSITE) {
          helper_ncols = 0;
        }
        ReleaseSysCache(rttup);
      }
    }

    uint64 slot_hash =
        pljs_fnv1a64(14695981039346656037ULL, sql_str, strlen(sql_str));
    slot_hash =
        pljs_fnv1a64(slot_hash, &n_helper_args, sizeof(n_helper_args));
    if (n_helper_args > 0) {
      slot_hash = pljs_fnv1a64(slot_hash, helper_arg_oids,
                               sizeof(Oid) * n_helper_args);
    }
    slot_hash = pljs_fnv1a64(slot_hash, &target_rettype, sizeof(Oid));
    slot_hash = pljs_fnv1a64(slot_hash, &helper_ncols, sizeof(helper_ncols));
    for (int i = 0; i < helper_ncols; i++) {
      slot_hash = pljs_fnv1a64(slot_hash, expected_cols[i].name,
                               strlen(expected_cols[i].name) + 1);
      slot_hash =
          pljs_fnv1a64(slot_hash, &expected_cols[i].type_oid, sizeof(Oid));
    }

    int base_slot = (int)(slot_hash % PLJS_NUM_INLINE_HELPERS);
    Oid helper_oid = InvalidOid;
    for (int probe = 0; probe < PLJS_NUM_INLINE_HELPERS; probe++) {
      int slot_idx = (base_slot + probe) % PLJS_NUM_INLINE_HELPERS;
      char helper_name[64];
      snprintf(helper_name, sizeof(helper_name), "pljs_inline_helper_%d",
               slot_idx);
      Oid cand_oid = pljs_lookup_func_oid_by_name_nargs(helper_name, -1);
      if (!OidIsValid(cand_oid)) {
        snprintf(helper_name, sizeof(helper_name), "plv8_inline_helper_%d",
                 slot_idx);
        cand_oid = pljs_lookup_func_oid_by_name_nargs(helper_name, -1);
      }
      if (!OidIsValid(cand_oid)) {
        snprintf(helper_name, sizeof(helper_name), "plpgq_inline_helper_%d",
                 slot_idx);
        cand_oid = pljs_lookup_func_oid_by_name_nargs(helper_name, -1);
      }
      if (!OidIsValid(cand_oid)) {
        continue;
      }

      bool in_use = false;
      if (root->parse != NULL) {
        ListCell *rlc;
        foreach (rlc, root->parse->rtable) {
          RangeTblEntry *rte = (RangeTblEntry *)lfirst(rlc);
          if (rte == target_rte || rte->rtekind != RTE_FUNCTION) {
            continue;
          }
          ListCell *flc;
          foreach (flc, rte->functions) {
            RangeTblFunction *rtf = (RangeTblFunction *)lfirst(flc);
            if (rtf->funcexpr && IsA(rtf->funcexpr, FuncExpr) &&
                ((FuncExpr *)rtf->funcexpr)->funcid == cand_oid) {
              in_use = true;
              break;
            }
          }
          if (in_use) {
            break;
          }
        }
      }
      if (!in_use) {
        helper_oid = cand_oid;
        break;
      }
      if (!OidIsValid(helper_oid)) {
        helper_oid = cand_oid;
      }
    }
    if (!OidIsValid(helper_oid)) {
      PG_RETURN_POINTER(NULL);
    }

    pljs_update_proc_table_columns(helper_oid, helper_ncols, expected_cols,
                                   sql_str, n_helper_args, helper_arg_oids,
                                   target_rettype);

    if (has_nonconst_arg) {
      target_rte->lateral = true;
    }

    FuncExpr *new_fexpr =
        makeFuncExpr(helper_oid, get_func_rettype(helper_oid), helper_args,
                     fexpr->funccollid, fexpr->inputcollid,
                     COERCE_EXPLICIT_CALL);
    new_fexpr->funcretset = true;

    PG_RETURN_POINTER(new_fexpr);
  }

  PG_RETURN_POINTER(NULL);
}

Datum pljs_base_type_in(PG_FUNCTION_ARGS) {
  char *s = PG_GETARG_CSTRING(0);
  if (s == NULL) {
    PG_RETURN_NULL();
  }

  Oid funcoid = fcinfo->flinfo->fn_oid;
  HeapTuple proc_tp = SearchSysCache1(PROCOID, ObjectIdGetDatum(funcoid));
  if (!HeapTupleIsValid(proc_tp)) {
    elog(ERROR, "cache lookup failed for function %u", funcoid);
  }
  Form_pg_proc proc = (Form_pg_proc)GETSTRUCT(proc_tp);
  Oid pronamespace = proc->pronamespace;
  char *proname = pstrdup(NameStr(proc->proname));
  Oid typoid = proc->prorettype;
  ReleaseSysCache(proc_tp);

  Oid argtypes[1] = {TEXTOID};
  List *qualname = list_make2(makeString(get_namespace_name(pronamespace)),
                              makeString(proname));
  Oid in_fn_oid = LookupFuncName(qualname, 1, argtypes, false);
  pfree(proname);

  HeapTuple tp = SearchSysCache1(TYPEOID, ObjectIdGetDatum(typoid));
  if (!HeapTupleIsValid(tp)) {
    elog(ERROR, "cache lookup failed for type %u", typoid);
  }
  Form_pg_type typtup = (Form_pg_type)GETSTRUCT(tp);
  int typeLen = typtup->typlen;
  char *typeName = pstrdup(NameStr(typtup->typname));
  ReleaseSysCache(tp);

  Datum datum =
      OidFunctionCall1Coll(in_fn_oid, InvalidOid, CStringGetTextDatum(s));
  bytea *result = DatumGetByteaPP(datum);
  if (typeLen >= 0) {
    int inputLen = VARSIZE_ANY_EXHDR(result) + VARHDRSZ;
    if (typeLen != inputLen) {
      elog(ERROR,
           "type %s is defined as fixed-size %d, but actual data length is %d",
           typeName, typeLen, inputLen);
    }
  }
  pfree(typeName);
  PG_RETURN_POINTER(result);
}

Datum pljs_base_type_out(PG_FUNCTION_ARGS) {
  Datum datum = PG_GETARG_DATUM(0);
  Oid funcoid = fcinfo->flinfo->fn_oid;
  HeapTuple proc_tp = SearchSysCache1(PROCOID, ObjectIdGetDatum(funcoid));
  if (!HeapTupleIsValid(proc_tp)) {
    elog(ERROR, "cache lookup failed for function %u", funcoid);
  }
  Form_pg_proc proc = (Form_pg_proc)GETSTRUCT(proc_tp);
  Oid pronamespace = proc->pronamespace;
  char *proname = pstrdup(NameStr(proc->proname));
  ReleaseSysCache(proc_tp);

  Oid out_argtypes[1] = {BYTEAOID};
  List *qualname = list_make2(makeString(get_namespace_name(pronamespace)),
                              makeString(proname));
  Oid out_fn_oid = LookupFuncName(qualname, 1, out_argtypes, false);
  pfree(proname);

  Datum result = OidFunctionCall1Coll(out_fn_oid, InvalidOid, datum);
  PG_RETURN_CSTRING(TextDatumGetCString(result));
}
