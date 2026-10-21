#ifndef __PLJS_FDW_H_
#define __PLJS_FDW_H_

#include "postgres.h"
#include "access/xact.h"
#include "deps/quickjs/quickjs.h"

void pljs_fdw_bootstrap_js(JSContext *ctx);
void pljs_fdw_context_reset(JSContext *ctx);
void pljs_fdw_relcache_cb(Datum arg, Oid relid);
void pljs_fdw_xact_cb(XactEvent event, void *arg);

Datum pljs_fdw_validator(PG_FUNCTION_ARGS);
Datum pljs_fdw_handler(PG_FUNCTION_ARGS);

#endif /* __PLJS_FDW_H_ */
