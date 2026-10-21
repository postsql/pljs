#include "postgres.h"

#include "access/htup_details.h"
#include "access/reloptions.h"
#include "access/sysattr.h"
#include "access/table.h"
#include "access/xact.h"
#include "catalog/pg_attribute.h"
#include "catalog/pg_foreign_data_wrapper.h"
#include "catalog/pg_foreign_server.h"
#include "catalog/pg_foreign_table.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_type.h"
#include "commands/defrem.h"
#include "commands/explain.h"
#if PG_VERSION_NUM >= 180000
#include "commands/explain_format.h"
#include "commands/explain_state.h"
#endif
#include "commands/vacuum.h"
#include "executor/executor.h"
#include "executor/tuptable.h"
#include "fmgr.h"
#include "foreign/fdwapi.h"
#include "foreign/foreign.h"
#include "miscadmin.h"
#include "nodes/execnodes.h"
#include "nodes/makefuncs.h"
#include "nodes/nodeFuncs.h"
#include "nodes/parsenodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "nodes/plannodes.h"
#include "nodes/value.h"
#include "optimizer/appendinfo.h"
#include "optimizer/clauses.h"
#include "optimizer/cost.h"
#include "optimizer/optimizer.h"
#include "optimizer/pathnode.h"
#include "optimizer/paths.h"
#include "optimizer/planmain.h"
#include "optimizer/restrictinfo.h"
#include "optimizer/tlist.h"
#include "parser/parse_oper.h"
#include "parser/parsetree.h"
#include "utils/builtins.h"
#include "utils/datum.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/rel.h"
#include "utils/syscache.h"
#include "utils/tuplestore.h"

#include "fdw.h"
#include "pljs.h"

#include <math.h>
#include <stdlib.h>
#include <string.h>

PG_FUNCTION_INFO_V1(pljs_fdw_validator);
PG_FUNCTION_INFO_V1(pljs_fdw_handler);

/*
 * Embedded JavaScript Bootstrap for ForeignDataWrapper and Reference Wrappers
 * (ArrayTableFdw, MapTableFdw, TempTableFdw, RandomPeopleFdw).
 * Exposed on globalThis, globalThis.pljs, and globalThis.plv8.
 */
static const char *pljs_fdw_bootstrap_code =
    "(function(global) {\n"
    "  if (global.ForeignDataWrapper) return;\n"
    "\n"
    "  class ForeignDataWrapper {\n"
    "    constructor(options = {}) {\n"
    "      this.options = options || {};\n"
    "      this.isKeyIndexed = false;\n"
    "    }\n"
    "    getRelSize(planContext) {\n"
    "      return { rows: 1000, width: 64, startupCost: 10.0, totalCost: 100.0 };\n"
    "    }\n"
    "    getPathKeys(planContext) {\n"
    "      return [];\n"
    "    }\n"
    "    scan(request) {\n"
    "      return [];\n"
    "    }\n"
    "    lookupKey(key, request) {\n"
    "      const req = Object.assign({}, request, { keys: [key], isKeyIndexed: true });\n"
    "      const res = this.scan(req);\n"
    "      if (Array.isArray(res)) return res;\n"
    "      if (res && typeof res[Symbol.iterator] === 'function') return Array.from(res);\n"
    "      return res ? [res] : [];\n"
    "    }\n"
    "    lookupKeys(keys, request) {\n"
    "      const out = [];\n"
    "      for (let i = 0; i < keys.length; i++) {\n"
    "        const r = this.lookupKey(keys[i], request);\n"
    "        if (Array.isArray(r)) {\n"
    "          for (let j = 0; j < r.length; j++) out.push(r[j]);\n"
    "        } else if (r) {\n"
    "          out.push(r);\n"
    "        }\n"
    "      }\n"
    "      return out;\n"
    "    }\n"
    "    insert(row) {\n"
    "      throw new Error(this.constructor.name + ': insert() is not implemented');\n"
    "    }\n"
    "    batchInsert(rows) {\n"
    "      const out = [];\n"
    "      for (let i = 0; i < rows.length; i++) {\n"
    "        out.push(this.insert(rows[i]));\n"
    "      }\n"
    "      return out;\n"
    "    }\n"
    "    update(rowid, newRow) {\n"
    "      throw new Error(this.constructor.name + ': update() is not implemented');\n"
    "    }\n"
    "    delete(rowid) {\n"
    "      throw new Error(this.constructor.name + ': delete() is not implemented');\n"
    "    }\n"
    "    canDirectModify(operation, quals) {\n"
    "      return false;\n"
    "    }\n"
    "    directModify(operation, quals, updates) {\n"
    "      throw new Error(this.constructor.name + ': directModify() is not implemented');\n"
    "    }\n"
    "    commit() {}\n"
    "    rollback() {}\n"
    "    static matchFilter(row, f) {\n"
    "      const v = row[f.column];\n"
    "      switch (f.op) {\n"
    "        case '=': return v == f.value;\n"
    "        case '<>':\n"
    "        case '!=': return v != f.value;\n"
    "        case '<': return v !== null && v !== undefined && v < f.value;\n"
    "        case '<=': return v !== null && v !== undefined && v <= f.value;\n"
    "        case '>': return v !== null && v !== undefined && v > f.value;\n"
    "        case '>=': return v !== null && v !== undefined && v >= f.value;\n"
    "        case 'IN': return Array.isArray(f.value) && f.value.some(x => x == v);\n"
    "        case 'NOT IN': return Array.isArray(f.value) && !f.value.some(x => x == v);\n"
    "        case 'IS NULL': return v === null || v === undefined;\n"
    "        case 'IS NOT NULL': return v !== null && v !== undefined;\n"
    "        case 'IS TRUE': return v === true;\n"
    "        case 'IS NOT TRUE': return v !== true;\n"
    "        case 'IS FALSE': return v === false;\n"
    "        case 'IS NOT FALSE': return v !== false;\n"
    "        case '~~': {\n"
    "          if (v === null || v === undefined) return false;\n"
    "          const pat = '^' + String(f.value).replace(/[.*+?^${}()|[\\]\\\\]/g, '\\\\$&').replace(/%/g, '.*').replace(/_/g, '.') + '$';\n"
    "          return new RegExp(pat).test(String(v));\n"
    "        }\n"
    "        case '~~*': {\n"
    "          if (v === null || v === undefined) return false;\n"
    "          const pat = '^' + String(f.value).replace(/[.*+?^${}()|[\\]\\\\]/g, '\\\\$&').replace(/%/g, '.*').replace(/_/g, '.') + '$';\n"
    "          return new RegExp(pat, 'i').test(String(v));\n"
    "        }\n"
    "        default: return true;\n"
    "      }\n"
    "    }\n"
    "    static matchFilters(row, filters) {\n"
    "      if (!filters || !filters.length) return true;\n"
    "      for (let i = 0; i < filters.length; i++) {\n"
    "        if (!ForeignDataWrapper.matchFilter(row, filters[i])) return false;\n"
    "      }\n"
    "      return true;\n"
    "    }\n"
    "    static projectRow(row, columns) {\n"
    "      if (!columns || !columns.length) return row;\n"
    "      const out = {};\n"
    "      for (let i = 0; i < columns.length; i++) {\n"
    "        const col = columns[i];\n"
    "        out[col] = row[col];\n"
    "      }\n"
    "      if (row.__rowid !== undefined) out.__rowid = row.__rowid;\n"
    "      return out;\n"
    "    }\n"
    "  }\n"
    "\n"
    "  class ArrayTableFdw extends ForeignDataWrapper {\n"
    "    constructor(options = {}) {\n"
    "      super(options);\n"
    "      this.isKeyIndexed = false;\n"
    "      this.rows = ArrayTableFdw.defaultRows();\n"
    "      this._txBackup = null;\n"
    "    }\n"
    "    static defaultRows() {\n"
    "      return [\n"
    "        { id: 101, username: 'alice',   dept_id: 1, role: 'eng',   salary: 140000 },\n"
    "        { id: 102, username: 'bob',     dept_id: 1, role: 'eng',   salary: 130000 },\n"
    "        { id: 103, username: 'charlie', dept_id: 2, role: 'sales', salary: 110000 },\n"
    "        { id: 104, username: 'david',   dept_id: 2, role: 'sales', salary: 115000 },\n"
    "        { id: 105, username: 'eva',     dept_id: 3, role: 'lead',  salary: 160000 },\n"
    "        { id: 106, username: 'frank',   dept_id: 1, role: 'eng',   salary: 125000 }\n"
    "      ];\n"
    "    }\n"
    "    _cloneRows() {\n"
    "      return this.rows.map(r => Object.assign({}, r));\n"
    "    }\n"
    "    _ensureBackup() {\n"
    "      if (this._txBackup === null) {\n"
    "        this._txBackup = this._cloneRows();\n"
    "      }\n"
    "    }\n"
    "    getRelSize(planContext) {\n"
    "      const n = this.rows.length || 1;\n"
    "      return { rows: n, width: 48, startupCost: 1.0, totalCost: 1.0 + n * 0.1 };\n"
    "    }\n"
    "    getPathKeys(planContext) {\n"
    "      return [{ column: 'id', ascending: true, nullsFirst: false }];\n"
    "    }\n"
    "    *scan(request) {\n"
    "      const filters = (request && request.filters) || [];\n"
    "      const cols = (request && request.columns) || null;\n"
    "      const lim = (request && typeof request.limit === 'number' && request.limit >= 0) ? request.limit : -1;\n"
    "      let count = 0;\n"
    "      for (let i = 0; i < this.rows.length; i++) {\n"
    "        if (lim >= 0 && count >= lim) break;\n"
    "        const r = this.rows[i];\n"
    "        if (ForeignDataWrapper.matchFilters(r, filters)) {\n"
    "          count++;\n"
    "          const out = ForeignDataWrapper.projectRow(r, cols);\n"
    "          out.__rowid = r.id;\n"
    "          yield out;\n"
    "        }\n"
    "      }\n"
    "    }\n"
    "    insert(row) {\n"
    "      this._ensureBackup();\n"
    "      const copy = Object.assign({}, row);\n"
    "      this.rows.push(copy);\n"
    "      this.rows.sort((a, b) => (a.id || 0) - (b.id || 0));\n"
    "      return copy;\n"
    "    }\n"
    "    update(rowid, newRow) {\n"
    "      this._ensureBackup();\n"
    "      const idx = this.rows.findIndex(r => r.id == rowid);\n"
    "      if (idx >= 0) {\n"
    "        this.rows[idx] = Object.assign({}, this.rows[idx], newRow);\n"
    "        return this.rows[idx];\n"
    "      }\n"
    "      return newRow;\n"
    "    }\n"
    "    delete(rowid) {\n"
    "      this._ensureBackup();\n"
    "      const idx = this.rows.findIndex(r => r.id == rowid);\n"
    "      if (idx >= 0) {\n"
    "        const removed = this.rows.splice(idx, 1)[0];\n"
    "        return removed;\n"
    "      }\n"
    "      return null;\n"
    "    }\n"
    "    commit() {\n"
    "      this._txBackup = null;\n"
    "    }\n"
    "    rollback() {\n"
    "      if (this._txBackup !== null) {\n"
    "        this.rows = this._txBackup;\n"
    "        this._txBackup = null;\n"
    "      }\n"
    "    }\n"
    "  }\n"
    "\n"
    "  class MapTableFdw extends ForeignDataWrapper {\n"
    "    constructor(options = {}) {\n"
    "      super(options);\n"
    "      this.isKeyIndexed = true;\n"
    "      this.keyColumn = (options && options.key) || (options && options.rowid_column) || 'key';\n"
    "      this.map = MapTableFdw.defaultMap();\n"
    "      this._txBackup = null;\n"
    "    }\n"
    "    static defaultMap() {\n"
    "      const m = new Map();\n"
    "      m.set('sess:1', { key: 'sess:1', user_id: 101, status: 'active',  data: { ip: '10.0.0.1', mfa: true } });\n"
    "      m.set('sess:2', { key: 'sess:2', user_id: 102, status: 'expired', data: { ip: '10.0.0.2', mfa: false } });\n"
    "      m.set('sess:3', { key: 'sess:3', user_id: 103, status: 'active',  data: { ip: '10.0.0.3', mfa: true } });\n"
    "      m.set('sess:4', { key: 'sess:4', user_id: 104, status: 'active',  data: { ip: '10.0.0.4', mfa: true } });\n"
    "      return m;\n"
    "    }\n"
    "    _cloneMap() {\n"
    "      const m = new Map();\n"
    "      for (const [k, v] of this.map.entries()) {\n"
    "        m.set(k, Object.assign({}, v));\n"
    "      }\n"
    "      return m;\n"
    "    }\n"
    "    _ensureBackup() {\n"
    "      if (this._txBackup === null) {\n"
    "        this._txBackup = this._cloneMap();\n"
    "      }\n"
    "    }\n"
    "    getRelSize(planContext) {\n"
    "      const hasKeyEq = planContext && Array.isArray(planContext.quals) &&\n"
    "        planContext.quals.some(q => q.column === this.keyColumn && (q.op === '=' || q.op === 'IN'));\n"
    "      if (hasKeyEq) {\n"
    "        return { rows: 1, width: 64, startupCost: 0.1, totalCost: 1.0 };\n"
    "      }\n"
    "      const n = this.map.size || 1;\n"
    "      return { rows: n, width: 64, startupCost: 1.0, totalCost: 1.0 + n * 0.2 };\n"
    "    }\n"
    "    lookupKey(key, request) {\n"
    "      const k = String(key);\n"
    "      if (!this.map.has(k)) return [];\n"
    "      const row = this.map.get(k);\n"
    "      const filters = (request && request.filters) || [];\n"
    "      if (!ForeignDataWrapper.matchFilters(row, filters)) return [];\n"
    "      const cols = (request && request.columns) || null;\n"
    "      const out = ForeignDataWrapper.projectRow(row, cols);\n"
    "      out.__rowid = k;\n"
    "      return [out];\n"
    "    }\n"
    "    *scan(request) {\n"
    "      const filters = (request && request.filters) || [];\n"
    "      const keys = (request && request.keys) || null;\n"
    "      const cols = (request && request.columns) || null;\n"
    "      const lim = (request && typeof request.limit === 'number' && request.limit >= 0) ? request.limit : -1;\n"
    "      let count = 0;\n"
    "      if (keys && keys.length > 0) {\n"
    "        for (let i = 0; i < keys.length; i++) {\n"
    "          if (lim >= 0 && count >= lim) break;\n"
    "          const found = this.lookupKey(keys[i], request);\n"
    "          for (let j = 0; j < found.length; j++) {\n"
    "            if (lim >= 0 && count >= lim) break;\n"
    "            count++;\n"
    "            yield found[j];\n"
    "          }\n"
    "        }\n"
    "        return;\n"
    "      }\n"
    "      for (const [k, row] of this.map.entries()) {\n"
    "        if (lim >= 0 && count >= lim) break;\n"
    "        if (ForeignDataWrapper.matchFilters(row, filters)) {\n"
    "          count++;\n"
    "          const out = ForeignDataWrapper.projectRow(row, cols);\n"
    "          out.__rowid = k;\n"
    "          yield out;\n"
    "        }\n"
    "      }\n"
    "    }\n"
    "    insert(row) {\n"
    "      this._ensureBackup();\n"
    "      const k = String(row[this.keyColumn]);\n"
    "      const copy = Object.assign({}, row);\n"
    "      this.map.set(k, copy);\n"
    "      return copy;\n"
    "    }\n"
    "    update(rowid, newRow) {\n"
    "      this._ensureBackup();\n"
    "      const oldK = String(rowid);\n"
    "      const existing = this.map.get(oldK) || {};\n"
    "      const merged = Object.assign({}, existing, newRow, { [this.keyColumn]: oldK });\n"
    "      const newK = merged[this.keyColumn] !== undefined && merged[this.keyColumn] !== null ? String(merged[this.keyColumn]) : oldK;\n"
    "      if (newK !== oldK) this.map.delete(oldK);\n"
    "      this.map.set(newK, merged);\n"
    "      return merged;\n"
    "    }\n"
    "    delete(rowid) {\n"
    "      this._ensureBackup();\n"
    "      const k = String(rowid); \n"
    "      const existing = this.map.get(k) || null;\n"
    "      this.map.delete(k);\n"
    "      return existing;\n"
    "    }\n"
    "    canDirectModify(operation, quals) {\n"
    "      return operation === 'DELETE' || operation === 'UPDATE';\n"
    "    }\n"
    "    directModify(operation, quals, updates) {\n"
    "      this._ensureBackup();\n"
    "      let affected = 0;\n"
    "      const toDelete = [];\n"
    "      const toUpdate = [];\n"
    "      for (const [k, row] of this.map.entries()) {\n"
    "        if (ForeignDataWrapper.matchFilters(row, quals)) {\n"
    "          if (operation === 'DELETE') {\n"
    "            toDelete.push(k);\n"
    "          } else if (operation === 'UPDATE') {\n"
    "            toUpdate.push([k, Object.assign({}, row, updates || {})]);\n"
    "          }\n"
    "        }\n"
    "      }\n"
    "      for (let i = 0; i < toDelete.length; i++) {\n"
    "        this.map.delete(toDelete[i]);\n"
    "        affected++;\n"
    "      }\n"
    "      for (let i = 0; i < toUpdate.length; i++) {\n"
    "        const [k, updated] = toUpdate[i];\n"
    "        this.map.set(k, updated);\n"
    "        affected++;\n"
    "      }\n"
    "      return affected;\n"
    "    }\n"
    "    commit() {\n"
    "      this._txBackup = null;\n"
    "    }\n"
    "    rollback() {\n"
    "      if (this._txBackup !== null) {\n"
    "        this.map = this._txBackup;\n"
    "        this._txBackup = null;\n"
    "      }\n"
    "    }\n"
    "  }\n"
    "\n"
    "  class TempTableFdw extends ForeignDataWrapper {\n"
    "    constructor(options = {}) {\n"
    "      super(options);\n"
    "      this.isKeyIndexed = true;\n"
    "      this.keyColumn = (options && (options.pk || options.key || options.rowid_column)) || 'id';\n"
    "      this.map = new Map();\n"
    "      this._txBackup = null;\n"
    "    }\n"
    "    _cloneMap() {\n"
    "      const m = new Map();\n"
    "      for (const [k, v] of this.map.entries()) {\n"
    "        m.set(k, Object.assign({}, v));\n"
    "      }\n"
    "      return m;\n"
    "    }\n"
    "    _ensureBackup() {\n"
    "      if (this._txBackup === null) {\n"
    "        this._txBackup = this._cloneMap();\n"
    "      }\n"
    "    }\n"
    "    _normKey(val) {\n"
    "      return val === null || val === undefined ? '' : String(val);\n"
    "    }\n"
    "    getRelSize(planContext) {\n"
    "      const hasKeyEq = planContext && Array.isArray(planContext.quals) &&\n"
    "        planContext.quals.some(q => q.column === this.keyColumn && (q.op === '=' || q.op === 'IN'));\n"
    "      if (hasKeyEq) {\n"
    "        return { rows: 1, width: 64, startupCost: 0.05, totalCost: 0.5 };\n"
    "      }\n"
    "      const n = this.map.size || 1;\n"
    "      return { rows: n, width: 64, startupCost: 0.5, totalCost: 0.5 + n * 0.1 };\n"
    "    }\n"
    "    getPathKeys(planContext) {\n"
    "      return [{ column: this.keyColumn, ascending: true, nullsFirst: false }];\n"
    "    }\n"
    "    lookupKey(key, request) {\n"
    "      const k = this._normKey(key);\n"
    "      if (!this.map.has(k)) return [];\n"
    "      const row = this.map.get(k);\n"
    "      const filters = (request && request.filters) || [];\n"
    "      if (!ForeignDataWrapper.matchFilters(row, filters)) return [];\n"
    "      const cols = (request && request.columns) || null;\n"
    "      const out = ForeignDataWrapper.projectRow(row, cols);\n"
    "      out.__rowid = row[this.keyColumn];\n"
    "      return [out];\n"
    "    }\n"
    "    *scan(request) {\n"
    "      const filters = (request && request.filters) || [];\n"
    "      const keys = (request && request.keys) || null;\n"
    "      const cols = (request && request.columns) || null;\n"
    "      const lim = (request && typeof request.limit === 'number' && request.limit >= 0) ? request.limit : -1;\n"
    "      let count = 0;\n"
    "      if (keys && keys.length > 0) {\n"
    "        for (let i = 0; i < keys.length; i++) {\n"
    "          if (lim >= 0 && count >= lim) break;\n"
    "          const found = this.lookupKey(keys[i], request);\n"
    "          for (let j = 0; j < found.length; j++) {\n"
    "            if (lim >= 0 && count >= lim) break;\n"
    "            count++;\n"
    "            yield found[j];\n"
    "          }\n"
    "        }\n"
    "        return;\n"
    "      }\n"
    "      for (const [, row] of this.map.entries()) {\n"
    "        if (lim >= 0 && count >= lim) break;\n"
    "        if (ForeignDataWrapper.matchFilters(row, filters)) {\n"
    "          count++;\n"
    "          const out = ForeignDataWrapper.projectRow(row, cols);\n"
    "          out.__rowid = row[this.keyColumn];\n"
    "          yield out;\n"
    "        }\n"
    "      }\n"
    "    }\n"
    "    insert(row) {\n"
    "      this._ensureBackup();\n"
    "      const k = this._normKey(row[this.keyColumn]);\n"
    "      if (!k) throw new Error('TempTableFdw: primary key column \"' + this.keyColumn + '\" cannot be null');\n"
    "      const copy = Object.assign({}, row);\n"
    "      this.map.set(k, copy);\n"
    "      return copy;\n"
    "    }\n"
    "    update(rowid, newRow) {\n"
    "      this._ensureBackup();\n"
    "      const oldK = this._normKey(rowid);\n"
    "      const existing = this.map.get(oldK) || {};\n"
    "      const merged = Object.assign({}, existing);\n"
    "      for (const prop of Object.keys(newRow)) {\n"
    "        if (newRow[prop] !== undefined) {\n"
    "          merged[prop] = newRow[prop];\n"
    "        }\n"
    "      }\n"
    "      const newK = merged[this.keyColumn] !== undefined && merged[this.keyColumn] !== null\n"
    "        ? this._normKey(merged[this.keyColumn])\n"
    "        : oldK;\n"
    "      if (newK !== oldK) this.map.delete(oldK);\n"
    "      this.map.set(newK, merged);\n"
    "      return merged;\n"
    "    }\n"
    "    delete(rowid) {\n"
    "      this._ensureBackup();\n"
    "      const k = this._normKey(rowid);\n"
    "      const existing = this.map.get(k) || null;\n"
    "      this.map.delete(k);\n"
    "      return existing;\n"
    "    }\n"
    "    canDirectModify(operation, quals) {\n"
    "      return operation === 'DELETE' || operation === 'UPDATE';\n"
    "    }\n"
    "    directModify(operation, quals, updates) {\n"
    "      this._ensureBackup();\n"
    "      let affected = 0;\n"
    "      const toDelete = [];\n"
    "      const toUpdate = [];\n"
    "      for (const [k, row] of this.map.entries()) {\n"
    "        if (ForeignDataWrapper.matchFilters(row, quals)) {\n"
    "          if (operation === 'DELETE') {\n"
    "            toDelete.push(k);\n"
    "          } else if (operation === 'UPDATE') {\n"
    "            toUpdate.push([k, Object.assign({}, row, updates || {})]);\n"
    "          }\n"
    "        }\n"
    "      }\n"
    "      for (let i = 0; i < toDelete.length; i++) {\n"
    "        this.map.delete(toDelete[i]);\n"
    "        affected++;\n"
    "      }\n"
    "      for (let i = 0; i < toUpdate.length; i++) {\n"
    "        const [k, updated] = toUpdate[i];\n"
    "        this.map.set(k, updated);\n"
    "        affected++;\n"
    "      }\n"
    "      return affected;\n"
    "    }\n"
    "    commit() {\n"
    "      this._txBackup = null;\n"
    "    }\n"
    "    rollback() {\n"
    "      if (this._txBackup !== null) {\n"
    "        this.map = this._txBackup;\n"
    "        this._txBackup = null;\n"
    "      }\n"
    "    }\n"
    "  }\n"
    "\n"
    "  class RandomPeopleFdw extends ForeignDataWrapper {\n"
    "    constructor(options = {}) {\n"
    "      super(options);\n"
    "      this.isKeyIndexed = true;\n"
    "      this.keyColumn = 'id';\n"
    "      this.seed = (options && options.seed !== undefined) ? (Number(options.seed) || 0) : 0;\n"
    "      this.defaultLimit = (options && options.limit !== undefined) ? Number(options.limit) : 1000;\n"
    "    }\n"
    "    static get FIRST_NAMES() {\n"
    "      return [\n"
    "        'James', 'Mary', 'John', 'Patricia', 'Robert', 'Jennifer', 'Michael', 'Linda',\n"
    "        'William', 'Elizabeth', 'David', 'Barbara', 'Richard', 'Susan', 'Joseph', 'Jessica',\n"
    "        'Thomas', 'Sarah', 'Charles', 'Karen', 'Christopher', 'Nancy', 'Daniel', 'Lisa',\n"
    "        'Matthew', 'Betty', 'Anthony', 'Margaret', 'Mark', 'Sandra'\n"
    "      ];\n"
    "    }\n"
    "    static get LAST_NAMES() {\n"
    "      return [\n"
    "        'Smith', 'Johnson', 'Williams', 'Brown', 'Jones', 'Garcia', 'Miller', 'Davis',\n"
    "        'Rodriguez', 'Martinez', 'Hernandez', 'Lopez', 'Gonzalez', 'Wilson', 'Anderson',\n"
    "        'Thomas', 'Taylor', 'Moore', 'Jackson', 'Martin', 'Lee', 'Perez', 'Thompson', 'White'\n"
    "      ];\n"
    "    }\n"
    "    static get CITIES() {\n"
    "      return [\n"
    "        'New York', 'Los Angeles', 'Chicago', 'Houston', 'Phoenix', 'Philadelphia',\n"
    "        'San Antonio', 'San Diego', 'Dallas', 'San Jose', 'Austin', 'Jacksonville',\n"
    "        'Fort Worth', 'Columbus', 'Charlotte', 'San Francisco', 'Indianapolis', 'Seattle'\n"
    "      ];\n"
    "    }\n"
    "    _generatePerson(id) {\n"
    "      let a = ((id + this.seed) * 1664525 + 1013904223) >>> 0;\n"
    "      const nextRand = () => {\n"
    "        a = (a + 0x6D2B79F5) >>> 0;\n"
    "        let t = Math.imul(a ^ (a >>> 15), 1 | a);\n"
    "        t ^= t + Math.imul(t ^ (t >>> 7), 61 | t);\n"
    "        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;\n"
    "      };\n"
    "      const fns = RandomPeopleFdw.FIRST_NAMES;\n"
    "      const lns = RandomPeopleFdw.LAST_NAMES;\n"
    "      const cities = RandomPeopleFdw.CITIES;\n"
    "      const fn = fns[Math.floor(nextRand() * fns.length)];\n"
    "      const ln = lns[Math.floor(nextRand() * lns.length)];\n"
    "      const city = cities[Math.floor(nextRand() * cities.length)];\n"
    "      const age = 18 + Math.floor(nextRand() * 65);\n"
    "      const email = fn.toLowerCase() + '.' + ln.toLowerCase() + id + '@example.com';\n"
    "      return {\n"
    "        id: id,\n"
    "        first_name: fn,\n"
    "        last_name: ln,\n"
    "        email: email,\n"
    "        age: age,\n"
    "        city: city,\n"
    "        __rowid: id\n"
    "      };\n"
    "    }\n"
    "    getRelSize(planContext) {\n"
    "      const hasKeyEq = planContext && Array.isArray(planContext.quals) &&\n"
    "        planContext.quals.some(q => q.column === 'id' && q.op === '=');\n"
    "      if (hasKeyEq) {\n"
    "        return { rows: 1, width: 72, startupCost: 0.05, totalCost: 0.5 };\n"
    "      }\n"
    "      const n = (planContext && typeof planContext.limit === 'number' && planContext.limit >= 0)\n"
    "        ? Math.min(planContext.limit, this.defaultLimit)\n"
    "        : this.defaultLimit;\n"
    "      return { rows: Math.max(1, n), width: 72, startupCost: 0.5, totalCost: 0.5 + Math.max(1, n) * 0.05 };\n"
    "    }\n"
    "    lookupKey(key, request) {\n"
    "      const id = Number(key);\n"
    "      if (!Number.isInteger(id) || id < 1 || id > this.defaultLimit) return [];\n"
    "      const row = this._generatePerson(id);\n"
    "      const cols = (request && request.columns) || null;\n"
    "      return [ForeignDataWrapper.projectRow(row, cols)];\n"
    "    }\n"
    "    *scan(request) {\n"
    "      const filters = (request && request.filters) || [];\n"
    "      const keys = (request && request.keys) || null;\n"
    "      const cols = (request && request.columns) || null;\n"
    "      const hasPushedLimit = (request && typeof request.limit === 'number' && request.limit >= 0);\n"
    "      const targetCount = hasPushedLimit ? Math.min(request.limit, this.defaultLimit) : this.defaultLimit;\n"
    "      if (targetCount <= 0) return;\n"
    "      let emitted = 0;\n"
    "      if (keys && keys.length > 0) {\n"
    "        const uniqueIds = Array.from(new Set(keys.map(v => Number(v)))).sort((a, b) => a - b);\n"
    "        for (let i = 0; i < uniqueIds.length; i++) {\n"
    "          if (emitted >= targetCount) break;\n"
    "          const found = this.lookupKey(uniqueIds[i], request);\n"
    "          for (let j = 0; j < found.length; j++) {\n"
    "            if (emitted >= targetCount) break;\n"
    "            emitted++;\n"
    "            yield found[j];\n"
    "          }\n"
    "        }\n"
    "        return;\n"
    "      }\n"
    "      for (let id = 1; id <= this.defaultLimit; id++) {\n"
    "        if (emitted >= targetCount) break;\n"
    "        const row = this._generatePerson(id);\n"
    "        if (ForeignDataWrapper.matchFilters(row, filters)) {\n"
    "          emitted++;\n"
    "          yield ForeignDataWrapper.projectRow(row, cols);\n"
    "        }\n"
    "      }\n"
    "    }\n"
    "  }\n"
    "\n"
    "  global.ForeignDataWrapper = ForeignDataWrapper;\n"
    "  global.ArrayTableFdw = ArrayTableFdw;\n"
    "  global.MapTableFdw = MapTableFdw;\n"
    "  global.TempTableFdw = TempTableFdw;\n"
    "  global.RandomPeopleFdw = RandomPeopleFdw;\n"
    "  if (global.pljs) {\n"
    "    global.pljs.ForeignDataWrapper = ForeignDataWrapper;\n"
    "    global.pljs.ArrayTableFdw = ArrayTableFdw;\n"
    "    global.pljs.MapTableFdw = MapTableFdw;\n"
    "    global.pljs.TempTableFdw = TempTableFdw;\n"
    "    global.pljs.RandomPeopleFdw = RandomPeopleFdw;\n"
    "  }\n"
    "  if (global.plv8) {\n"
    "    global.plv8.ForeignDataWrapper = ForeignDataWrapper;\n"
    "    global.plv8.ArrayTableFdw = ArrayTableFdw;\n"
    "    global.plv8.MapTableFdw = MapTableFdw;\n"
    "    global.plv8.TempTableFdw = TempTableFdw;\n"
    "    global.plv8.RandomPeopleFdw = RandomPeopleFdw;\n"
    "  }\n"
    "})(globalThis);\n";

void pljs_fdw_bootstrap_js(JSContext *ctx) {
  JSValue res = JS_Eval(ctx, pljs_fdw_bootstrap_code,
                        strlen(pljs_fdw_bootstrap_code), "<pljs_fdw_bootstrap>",
                        JS_EVAL_TYPE_GLOBAL);
  if (JS_IsException(res)) {
    JS_FreeValue(ctx, JS_GetException(ctx));
  }
  JS_FreeValue(ctx, res);
}

/*
 * ---------- Options Extraction ----------
 */

typedef struct PljsFdwOptEntry {
  char *key;
  char *val;
} PljsFdwOptEntry;

typedef struct PljsFdwOptions {
  int count;
  int capacity;
  PljsFdwOptEntry *entries;
} PljsFdwOptions;

static void pljs_fdw_opt_set(PljsFdwOptions *opts, const char *key,
                             const char *val) {
  for (int i = 0; i < opts->count; i++) {
    if (strcmp(opts->entries[i].key, key) == 0) {
      pfree(opts->entries[i].val);
      opts->entries[i].val = pstrdup(val);
      return;
    }
  }
  if (opts->count >= opts->capacity) {
    int new_cap = opts->capacity == 0 ? 8 : opts->capacity * 2;
    if (opts->entries == NULL) {
      opts->entries =
          (PljsFdwOptEntry *)palloc(sizeof(PljsFdwOptEntry) * new_cap);
    } else {
      opts->entries = (PljsFdwOptEntry *)repalloc(
          opts->entries, sizeof(PljsFdwOptEntry) * new_cap);
    }
    opts->capacity = new_cap;
  }
  opts->entries[opts->count].key = pstrdup(key);
  opts->entries[opts->count].val = pstrdup(val);
  opts->count++;
}

static const char *pljs_fdw_opt_get(const PljsFdwOptions *opts,
                                    const char *key) {
  for (int i = 0; i < opts->count; i++) {
    if (strcmp(opts->entries[i].key, key) == 0) {
      return opts->entries[i].val;
    }
  }
  return NULL;
}

static void pljs_fdw_get_options(Oid foreigntableid, PljsFdwOptions *opts) {
  memset(opts, 0, sizeof(*opts));
  ForeignTable *ft = GetForeignTable(foreigntableid);
  ForeignServer *fs = GetForeignServer(ft->serverid);

  ListCell *lc;
  foreach (lc, fs->options) {
    DefElem *def = (DefElem *)lfirst(lc);
    pljs_fdw_opt_set(opts, def->defname, defGetString(def));
  }
  foreach (lc, ft->options) {
    DefElem *def = (DefElem *)lfirst(lc);
    pljs_fdw_opt_set(opts, def->defname, defGetString(def));
  }
}

/*
 * ---------- Session Wrapper Cache ----------
 */

typedef struct PljsFdwCachedWrapper {
  Oid user_id;
  Oid foreigntableid;
  JSContext *ctx;
  JSValue instance;
  struct PljsFdwCachedWrapper *next;
} PljsFdwCachedWrapper;

static PljsFdwCachedWrapper *pljs_fdw_wrapper_head = NULL;

void pljs_fdw_context_reset(JSContext *ctx) {
  PljsFdwCachedWrapper **pp = &pljs_fdw_wrapper_head;
  while (*pp != NULL) {
    PljsFdwCachedWrapper *curr = *pp;
    if (ctx == NULL || curr->ctx == ctx) {
      *pp = curr->next;
      if (curr->ctx != NULL && !JS_IsUndefined(curr->instance)) {
        JS_FreeValue(curr->ctx, curr->instance);
      }
      pfree(curr);
    } else {
      pp = &curr->next;
    }
  }
}

void pljs_fdw_relcache_cb(Datum arg, Oid relid) {
  (void)arg;
  PljsFdwCachedWrapper **pp = &pljs_fdw_wrapper_head;
  while (*pp != NULL) {
    PljsFdwCachedWrapper *curr = *pp;
    if (relid == InvalidOid || curr->foreigntableid == relid) {
      *pp = curr->next;
      if (curr->ctx != NULL && !JS_IsUndefined(curr->instance)) {
        JS_FreeValue(curr->ctx, curr->instance);
      }
      pfree(curr);
    } else {
      pp = &curr->next;
    }
  }
}

void pljs_fdw_xact_cb(XactEvent event, void *arg) {
  (void)arg;
  if (event != XACT_EVENT_COMMIT && event != XACT_EVENT_ABORT &&
      event != XACT_EVENT_PARALLEL_COMMIT &&
      event != XACT_EVENT_PARALLEL_ABORT) {
    return;
  }

  const char *method_name =
      (event == XACT_EVENT_COMMIT || event == XACT_EVENT_PARALLEL_COMMIT)
          ? "commit"
          : "rollback";

  for (PljsFdwCachedWrapper *curr = pljs_fdw_wrapper_head; curr != NULL;
       curr = curr->next) {
    if (curr->ctx == NULL || JS_IsUndefined(curr->instance))
      continue;
    JSContext *ctx = curr->ctx;
    JSValue fn = JS_GetPropertyStr(ctx, curr->instance, method_name);
    if (JS_IsFunction(ctx, fn)) {
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue ret = JS_Call(ctx, fn, curr->instance, 0, NULL);
      if (JS_IsException(ret)) {
        JS_FreeValue(ctx, JS_GetException(ctx));
      }
      JS_FreeValue(ctx, ret);
    } else if (JS_IsException(fn)) {
      JS_FreeValue(ctx, JS_GetException(ctx));
    }
    JS_FreeValue(ctx, fn);
  }
}

static JSContext *pljs_fdw_get_context(void) {
  Oid user_id = GetUserId();
  pljs_context_cache_value *entry = pljs_cache_context_find(user_id, user_id);
  if (entry != NULL) {
    return entry->ctx;
  }
  return pljs_create_context(user_id, user_id);
}

static JSValue pljs_fdw_get_wrapper_instance(JSContext *ctx,
                                             Oid foreigntableid,
                                             const PljsFdwOptions *opts) {
  Oid user_id = GetUserId();
  for (PljsFdwCachedWrapper *curr = pljs_fdw_wrapper_head; curr != NULL;
       curr = curr->next) {
    if (curr->user_id == user_id && curr->foreigntableid == foreigntableid &&
        curr->ctx == ctx && !JS_IsUndefined(curr->instance)) {
      return JS_DupValue(ctx, curr->instance);
    }
  }

  pljs_fdw_bootstrap_js(ctx);

  const char *wrapper_name = pljs_fdw_opt_get(opts, "wrapper");
  if (wrapper_name == NULL || wrapper_name[0] == '\0') {
    wrapper_name = "ArrayTableFdw";
  }

  JSValue global_obj = JS_GetGlobalObject(ctx);
  JSValue ctor_val = JS_GetPropertyStr(ctx, global_obj, wrapper_name);
  if (JS_IsUndefined(ctor_val)) {
    JSValue pljs_obj = JS_GetPropertyStr(ctx, global_obj, "pljs");
    if (JS_IsObject(pljs_obj)) {
      JS_FreeValue(ctx, ctor_val);
      ctor_val = JS_GetPropertyStr(ctx, pljs_obj, wrapper_name);
    }
    JS_FreeValue(ctx, pljs_obj);
  }
  if (JS_IsUndefined(ctor_val)) {
    JSValue plv8_obj = JS_GetPropertyStr(ctx, global_obj, "plv8");
    if (JS_IsObject(plv8_obj)) {
      JS_FreeValue(ctx, ctor_val);
      ctor_val = JS_GetPropertyStr(ctx, plv8_obj, wrapper_name);
    }
    JS_FreeValue(ctx, plv8_obj);
  }
  JS_FreeValue(ctx, global_obj);

  if (JS_IsException(ctor_val)) {
    pljs_ereport_js_exception(ctx);
  }

  if (!JS_IsObject(ctor_val)) {
    JS_FreeValue(ctx, ctor_val);
    ereport(ERROR,
            (errcode(ERRCODE_FDW_INVALID_OPTION_NAME),
             errmsg("pljs_fdw: JavaScript wrapper \"%s\" not found on globalThis or pljs",
                    wrapper_name)));
  }

  JSValue js_opts = JS_NewObject(ctx);
  for (int i = 0; i < opts->count; i++) {
    JS_SetPropertyStr(ctx, js_opts, opts->entries[i].key,
                      JS_NewString(ctx, opts->entries[i].val));
  }
  JS_SetPropertyStr(ctx, js_opts, "tableOid",
                    JS_NewUint32(ctx, (uint32_t)foreigntableid));

  JSValue instance = JS_UNDEFINED;
  if (JS_IsConstructor(ctx, ctor_val)) {
    JSValue args[1] = {js_opts};
    JS_UpdateStackTop(JS_GetRuntime(ctx));
    instance = JS_CallConstructor(ctx, ctor_val, 1, args);
    JS_FreeValue(ctx, js_opts);
    JS_FreeValue(ctx, ctor_val);
    if (JS_IsException(instance)) {
      pljs_ereport_js_exception(ctx);
    }
  } else if (JS_IsFunction(ctx, ctor_val)) {
    JSValue args[1] = {js_opts};
    JS_UpdateStackTop(JS_GetRuntime(ctx));
    instance = JS_Call(ctx, ctor_val, JS_UNDEFINED, 1, args);
    JS_FreeValue(ctx, js_opts);
    JS_FreeValue(ctx, ctor_val);
    if (JS_IsException(instance)) {
      pljs_ereport_js_exception(ctx);
    }
    if (!JS_IsObject(instance)) {
      JS_FreeValue(ctx, instance);
      ereport(ERROR,
              (errcode(ERRCODE_FDW_ERROR),
               errmsg("pljs_fdw: wrapper factory \"%s\" did not return an object",
                      wrapper_name)));
    }
  } else {
    JS_FreeValue(ctx, js_opts);
    instance = ctor_val;
  }

  PljsFdwCachedWrapper *entry = (PljsFdwCachedWrapper *)MemoryContextAllocZero(
      TopMemoryContext, sizeof(PljsFdwCachedWrapper));
  entry->user_id = user_id;
  entry->foreigntableid = foreigntableid;
  entry->ctx = ctx;
  entry->instance = JS_DupValue(ctx, instance);
  entry->next = pljs_fdw_wrapper_head;
  pljs_fdw_wrapper_head = entry;

  return instance;
}

/*
 * ---------- Qualifier Pushdown & Extraction ----------
 */

typedef enum PljsQualKind {
  QUAL_OP,
  QUAL_SAOP_IN,
  QUAL_SAOP_NOT_IN,
  QUAL_NULLTEST_IS_NULL,
  QUAL_NULLTEST_IS_NOT_NULL,
  QUAL_BOOLTEST_IS_TRUE,
  QUAL_BOOLTEST_IS_NOT_TRUE,
  QUAL_BOOLTEST_IS_FALSE,
  QUAL_BOOLTEST_IS_NOT_FALSE
} PljsQualKind;

typedef struct PljsQual {
  AttrNumber attnum;
  char *colname;
  char *opname;
  PljsQualKind kind;
  bool is_param;
  Expr *right_expr;
  ExprState *expr_state;
  Oid const_type;
  Datum const_val;
  bool const_isnull;
} PljsQual;

typedef struct PljsOrderBy {
  char *colname;
  bool ascending;
  bool nulls_first;
} PljsOrderBy;

typedef struct PljsFdwPlanState {
  Oid foreigntableid;
  bool is_key_indexed;
  char *key_column;
  bool cache_results;
  int cache_size;
  int64 cache_memory_limit;
  List *pushable_clauses;
  int pushed_quals_count;
  PljsQual *pushed_quals;
  int orderby_count;
  PljsOrderBy *orderby;
  int64 pushed_limit;
} PljsFdwPlanState;

typedef struct PljsCacheEntry {
  char *key;
  Tuplestorestate *store;
  bool complete;
  int64 bytes;
  struct PljsCacheEntry *prev;
  struct PljsCacheEntry *next;
} PljsCacheEntry;

typedef struct PljsFdwScanState {
  Oid user_id;
  JSContext *ctx;
  JSValue wrapper_instance;
  JSValue iter_or_array;
  bool is_generator;
  bool is_array;
  bool is_func;
  uint32_t row_idx;
  uint32_t row_count;
  bool scan_started;
  bool eof_reached;

  Oid foreigntableid;
  bool is_key_indexed;
  char *key_column;
  char *rowid_column;
  AttrNumber rowid_attno;

  int quals_count;
  PljsQual *quals;
  int orderby_count;
  PljsOrderBy *orderby;
  int proj_cols_count;
  char **proj_cols;
  int64 pushed_limit;
  int64 emitted_rows;

  bool cache_results;
  int cache_max_entries;
  int64 cache_max_bytes;
  int64 cache_current_bytes;
  int cache_entry_count;

  Tuplestorestate *tuplestore;
  bool reading_from_tuplestore;
  PljsCacheEntry *active_cache_entry;

  PljsCacheEntry *lru_head;
  PljsCacheEntry *lru_tail;

  int64 stats_cache_hits;
  int64 stats_cache_misses;

  MemoryContext scan_mcxt;
  MemoryContext row_cxt;
  MemoryContextCallback cleanup_cb;
  FmgrInfo type_io_flinfo;
} PljsFdwScanState;

typedef struct PljsFdwModifyState {
  Oid user_id;
  JSContext *ctx;
  JSValue wrapper_instance;
  Oid foreigntableid;
  CmdType operation;
  char *rowid_column;
  AttrNumber rowid_attno;
  Oid rowid_type;
  int batch_size;
  MemoryContext modify_mcxt;
  MemoryContextCallback cleanup_cb;
  FmgrInfo type_io_flinfo;
} PljsFdwModifyState;

typedef struct PljsFdwDirectModifyState {
  Oid user_id;
  JSContext *ctx;
  JSValue wrapper_instance;
  CmdType operation;
  int quals_count;
  PljsQual *quals;
  bool has_executed;
  int64 affected_rows;
  bool set_processed;
  MemoryContext direct_mcxt;
  MemoryContextCallback cleanup_cb;
  FmgrInfo type_io_flinfo;
} PljsFdwDirectModifyState;

static bool pljs_fdw_ctx_is_alive(Oid user_id, JSContext *ctx) {
  if (ctx == NULL || !OidIsValid(user_id))
    return false;
  pljs_context_cache_value *entry = pljs_cache_context_find(user_id, user_id);
  return (entry != NULL && entry->ctx == ctx);
}

static void pljs_fdw_scan_cleanup_cb(void *arg) {
  PljsFdwScanState *festate = (PljsFdwScanState *)arg;
  if (!festate)
    return;
  if (pljs_fdw_ctx_is_alive(festate->user_id, festate->ctx)) {
    if (!JS_IsUndefined(festate->iter_or_array)) {
      JS_FreeValue(festate->ctx, festate->iter_or_array);
      festate->iter_or_array = JS_UNDEFINED;
    }
    if (!JS_IsUndefined(festate->wrapper_instance)) {
      JS_FreeValue(festate->ctx, festate->wrapper_instance);
      festate->wrapper_instance = JS_UNDEFINED;
    }
  }
}

static void pljs_fdw_modify_cleanup_cb(void *arg) {
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)arg;
  if (!fmstate)
    return;
  if (pljs_fdw_ctx_is_alive(fmstate->user_id, fmstate->ctx)) {
    if (!JS_IsUndefined(fmstate->wrapper_instance)) {
      JS_FreeValue(fmstate->ctx, fmstate->wrapper_instance);
      fmstate->wrapper_instance = JS_UNDEFINED;
    }
  }
}

static void pljs_fdw_direct_modify_cleanup_cb(void *arg) {
  PljsFdwDirectModifyState *dmstate = (PljsFdwDirectModifyState *)arg;
  if (!dmstate)
    return;
  if (pljs_fdw_ctx_is_alive(dmstate->user_id, dmstate->ctx)) {
    if (!JS_IsUndefined(dmstate->wrapper_instance)) {
      JS_FreeValue(dmstate->ctx, dmstate->wrapper_instance);
      dmstate->wrapper_instance = JS_UNDEFINED;
    }
  }
}

static Expr *pljs_fdw_strip_relabel(Expr *expr) {
  while (expr && IsA(expr, RelabelType)) {
    expr = ((RelabelType *)expr)->arg;
  }
  return expr;
}

static bool pljs_fdw_is_Supported_op(const char *opname) {
  static const char *supported[] = {"=",  "<>", "!=",  "<",   "<=",
                                    ">",  ">=", "~~",  "~~*", NULL};
  for (int i = 0; supported[i] != NULL; i++) {
    if (strcmp(opname, supported[i]) == 0)
      return true;
  }
  return false;
}

static const char *pljs_fdw_commute_op(const char *opname) {
  if (strcmp(opname, "=") == 0)
    return "=";
  if (strcmp(opname, "<>") == 0 || strcmp(opname, "!=") == 0)
    return opname;
  if (strcmp(opname, "<") == 0)
    return ">";
  if (strcmp(opname, "<=") == 0)
    return ">=";
  if (strcmp(opname, ">") == 0)
    return "<";
  if (strcmp(opname, ">=") == 0)
    return "<=";
  return NULL;
}

static bool pljs_fdw_extract_qual(Node *clause, Index scanrelid,
                                  TupleDesc tupdesc, PljsQual *out) {
  memset(out, 0, sizeof(*out));
  if (!clause)
    return false;

  if (IsA(clause, OpExpr)) {
    OpExpr *op = (OpExpr *)clause;
    if (list_length(op->args) != 2)
      return false;

    char *opname = get_opname(op->opno);
    if (!opname)
      return false;

    Expr *left = pljs_fdw_strip_relabel((Expr *)linitial(op->args));
    Expr *right = pljs_fdw_strip_relabel((Expr *)lsecond(op->args));

    Var *var = NULL;
    Expr *other = NULL;
    const char *final_op = opname;

    if (IsA(left, Var) && (Index)((Var *)left)->varno == scanrelid &&
        ((Var *)left)->varattno > 0) {
      var = (Var *)left;
      other = right;
    } else if (IsA(right, Var) && (Index)((Var *)right)->varno == scanrelid &&
               ((Var *)right)->varattno > 0) {
      var = (Var *)right;
      other = left;
      final_op = pljs_fdw_commute_op(opname);
      if (!final_op)
        return false;
    } else {
      return false;
    }

    if (!pljs_fdw_is_Supported_op(final_op))
      return false;

    if (var->varattno > tupdesc->natts)
      return false;
    Form_pg_attribute attr = TupleDescAttr(tupdesc, var->varattno - 1);
    if (attr->attisdropped)
      return false;

    if (IsA(other, Const)) {
      Const *c = (Const *)other;
      out->attnum = var->varattno;
      out->colname = pstrdup(NameStr(attr->attname));
      out->opname = pstrdup(final_op);
      out->kind = QUAL_OP;
      out->is_param = false;
      out->const_type = c->consttype;
      out->const_val = c->constvalue;
      out->const_isnull = c->constisnull;
      return true;
    } else if (IsA(other, Param) || IsA(other, Var)) {
      if (IsA(other, Var) && (Index)((Var *)other)->varno == scanrelid)
        return false;
      out->attnum = var->varattno;
      out->colname = pstrdup(NameStr(attr->attname));
      out->opname = pstrdup(final_op);
      out->kind = QUAL_OP;
      out->is_param = true;
      out->right_expr = other;
      out->const_type = exprType((Node *)other);
      return true;
    }
    return false;
  }

  if (IsA(clause, ScalarArrayOpExpr)) {
    ScalarArrayOpExpr *saop = (ScalarArrayOpExpr *)clause;
    if (list_length(saop->args) != 2)
      return false;

    char *opname = get_opname(saop->opno);
    if (!opname)
      return false;

    bool is_eq = (strcmp(opname, "=") == 0);
    bool is_neq = (strcmp(opname, "<>") == 0 || strcmp(opname, "!=") == 0);
    if ((is_eq && !saop->useOr) || (is_neq && saop->useOr) ||
        (!is_eq && !is_neq))
      return false;

    Expr *left = pljs_fdw_strip_relabel((Expr *)linitial(saop->args));
    Expr *right = pljs_fdw_strip_relabel((Expr *)lsecond(saop->args));

    if (!IsA(left, Var))
      return false;
    Var *var = (Var *)left;
    if ((Index)var->varno != scanrelid || var->varattno <= 0 ||
        var->varattno > tupdesc->natts)
      return false;

    Form_pg_attribute attr = TupleDescAttr(tupdesc, var->varattno - 1);
    if (attr->attisdropped)
      return false;

    if (IsA(right, Const)) {
      Const *c = (Const *)right;
      out->attnum = var->varattno;
      out->colname = pstrdup(NameStr(attr->attname));
      out->opname = pstrdup(is_eq ? "IN" : "NOT IN");
      out->kind = is_eq ? QUAL_SAOP_IN : QUAL_SAOP_NOT_IN;
      out->is_param = false;
      out->const_type = c->consttype;
      out->const_val = c->constvalue;
      out->const_isnull = c->constisnull;
      return true;
    } else if (IsA(right, Param)) {
      out->attnum = var->varattno;
      out->colname = pstrdup(NameStr(attr->attname));
      out->opname = pstrdup(is_eq ? "IN" : "NOT IN");
      out->kind = is_eq ? QUAL_SAOP_IN : QUAL_SAOP_NOT_IN;
      out->is_param = true;
      out->right_expr = right;
      out->const_type = exprType((Node *)right);
      return true;
    }
    return false;
  }

  if (IsA(clause, NullTest)) {
    NullTest *nt = (NullTest *)clause;
    Expr *arg = pljs_fdw_strip_relabel(nt->arg);
    if (!IsA(arg, Var))
      return false;
    Var *var = (Var *)arg;
    if ((Index)var->varno != scanrelid || var->varattno <= 0 ||
        var->varattno > tupdesc->natts)
      return false;

    Form_pg_attribute attr = TupleDescAttr(tupdesc, var->varattno - 1);
    if (attr->attisdropped)
      return false;

    out->attnum = var->varattno;
    out->colname = pstrdup(NameStr(attr->attname));
    out->opname =
        pstrdup((nt->nulltesttype == IS_NULL) ? "IS NULL" : "IS NOT NULL");
    out->kind = (nt->nulltesttype == IS_NULL) ? QUAL_NULLTEST_IS_NULL
                                              : QUAL_NULLTEST_IS_NOT_NULL;
    out->is_param = false;
    out->const_isnull = true;
    return true;
  }

  if (IsA(clause, BooleanTest)) {
    BooleanTest *bt = (BooleanTest *)clause;
    Expr *arg = pljs_fdw_strip_relabel(bt->arg);
    if (!IsA(arg, Var))
      return false;
    Var *var = (Var *)arg;
    if ((Index)var->varno != scanrelid || var->varattno <= 0 ||
        var->varattno > tupdesc->natts)
      return false;

    Form_pg_attribute attr = TupleDescAttr(tupdesc, var->varattno - 1);
    if (attr->attisdropped)
      return false;

    out->attnum = var->varattno;
    out->colname = pstrdup(NameStr(attr->attname));
    switch (bt->booltesttype) {
    case IS_TRUE:
      out->opname = pstrdup("IS TRUE");
      out->kind = QUAL_BOOLTEST_IS_TRUE;
      break;
    case IS_NOT_TRUE:
      out->opname = pstrdup("IS NOT TRUE");
      out->kind = QUAL_BOOLTEST_IS_NOT_TRUE;
      break;
    case IS_FALSE:
      out->opname = pstrdup("IS FALSE");
      out->kind = QUAL_BOOLTEST_IS_FALSE;
      break;
    case IS_NOT_FALSE:
      out->opname = pstrdup("IS NOT FALSE");
      out->kind = QUAL_BOOLTEST_IS_NOT_FALSE;
      break;
    default:
      return false;
    }
    out->is_param = false;
    out->const_isnull = true;
    return true;
  }

  return false;
}

static JSValue pljs_fdw_qual_to_js(JSContext *ctx, const PljsQual *q,
                                   ExprContext *econtext) {
  JSValue obj = JS_NewObject(ctx);
  JS_SetPropertyStr(ctx, obj, "column", JS_NewString(ctx, q->colname));
  JS_SetPropertyStr(ctx, obj, "op", JS_NewString(ctx, q->opname));
  JS_SetPropertyStr(ctx, obj, "attnum", JS_NewInt32(ctx, q->attnum));
  JS_SetPropertyStr(ctx, obj, "isParam", JS_NewBool(ctx, q->is_param));

  if (q->kind == QUAL_NULLTEST_IS_NULL ||
      q->kind == QUAL_NULLTEST_IS_NOT_NULL ||
      q->kind == QUAL_BOOLTEST_IS_TRUE ||
      q->kind == QUAL_BOOLTEST_IS_NOT_TRUE ||
      q->kind == QUAL_BOOLTEST_IS_FALSE ||
      q->kind == QUAL_BOOLTEST_IS_NOT_FALSE) {
    JS_SetPropertyStr(ctx, obj, "value", JS_NULL);
    return obj;
  }

  Datum val = q->const_val;
  bool isnull = q->const_isnull;
  if (q->is_param && q->expr_state != NULL && econtext != NULL) {
    val = ExecEvalExpr(q->expr_state, econtext, &isnull);
  }

  if (isnull || (q->is_param && q->expr_state == NULL)) {
    JS_SetPropertyStr(ctx, obj, "value", JS_NULL);
  } else {
    JSValue js_val = pljs_datum_to_jsvalue(q->const_type, val, false, true, ctx);
    if (JS_IsException(js_val)) {
      JS_FreeValue(ctx, obj);
      pljs_ereport_js_exception(ctx);
    }
    JS_SetPropertyStr(ctx, obj, "value", js_val);
  }

  return obj;
}

/*
 * ----------FDW Planner Callbacks ----------
 */

static void pljs_fdw_get_foreign_rel_size(PlannerInfo *root,
                                          RelOptInfo *baserel,
                                          Oid foreigntableid) {
  PljsFdwPlanState *fpinfo =
      (PljsFdwPlanState *)palloc0(sizeof(PljsFdwPlanState));
  fpinfo->foreigntableid = foreigntableid;
  fpinfo->is_key_indexed = false;
  fpinfo->key_column = pstrdup("key");
  fpinfo->cache_results = true;
  fpinfo->cache_size = 64;
  fpinfo->cache_memory_limit = 16LL * 1024LL * 1024LL;
  fpinfo->pushed_limit = -1;

  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);

  const char *opt_cr = pljs_fdw_opt_get(&opts, "cache_results");
  if (opt_cr && (strcmp(opt_cr, "false") == 0 || strcmp(opt_cr, "off") == 0 ||
                 strcmp(opt_cr, "0") == 0)) {
    fpinfo->cache_results = false;
  }
  const char *opt_cs = pljs_fdw_opt_get(&opts, "cache_size");
  if (opt_cs) {
    int cs = atoi(opt_cs);
    if (cs > 0)
      fpinfo->cache_size = cs;
  }
  const char *opt_cm = pljs_fdw_opt_get(&opts, "cache_memory_limit");
  if (opt_cm) {
    long long cm = atoll(opt_cm);
    if (cm > 0)
      fpinfo->cache_memory_limit = (int64)cm;
  }
  const char *opt_key = pljs_fdw_opt_get(&opts, "key");
  if (opt_key && opt_key[0] != '\0') {
    fpinfo->key_column = pstrdup(opt_key);
  } else {
    const char *opt_pk = pljs_fdw_opt_get(&opts, "pk");
    if (opt_pk && opt_pk[0] != '\0') {
      fpinfo->key_column = pstrdup(opt_pk);
    } else {
      const char *opt_rc = pljs_fdw_opt_get(&opts, "rowid_column");
      if (opt_rc && opt_rc[0] != '\0') {
        fpinfo->key_column = pstrdup(opt_rc);
      }
    }
  }

  Relation rel = table_open(foreigntableid, NoLock);
  TupleDesc tupdesc = RelationGetDescr(rel);

  int n_rinfo = list_length(baserel->baserestrictinfo);
  if (n_rinfo > 0) {
    fpinfo->pushed_quals =
        (PljsQual *)palloc0(sizeof(PljsQual) * (size_t)n_rinfo);
  }

  ListCell *lc;
  foreach (lc, baserel->baserestrictinfo) {
    RestrictInfo *rinfo = (RestrictInfo *)lfirst(lc);
    PljsQual q;
    if (pljs_fdw_extract_qual((Node *)rinfo->clause, baserel->relid, tupdesc,
                              &q)) {
      fpinfo->pushed_quals[fpinfo->pushed_quals_count++] = q;
      fpinfo->pushable_clauses = lappend(fpinfo->pushable_clauses, rinfo);
    }
  }

  table_close(rel, NoLock);

  if (root->parse && list_length(root->parse->rtable) == 1 &&
      root->parse->jointree && list_length(root->parse->jointree->fromlist) == 1 &&
      root->parse->jointree->quals == NULL && !root->parse->hasAggs &&
      root->parse->groupClause == NIL && root->parse->distinctClause == NIL &&
      root->parse->havingQual == NULL && root->parse->limitCount != NULL &&
      IsA(root->parse->limitCount, Const)) {
    Const *lim_const = (Const *)root->parse->limitCount;
    int64 lim_val = -1;
    if (!lim_const->constisnull) {
      if (lim_const->consttype == INT8OID)
        lim_val = DatumGetInt64(lim_const->constvalue);
      else if (lim_const->consttype == INT4OID)
        lim_val = (int64)DatumGetInt32(lim_const->constvalue);
    }
    int64 off_val = 0;
    if (root->parse->limitOffset != NULL) {
      if (IsA(root->parse->limitOffset, Const)) {
        Const *off_const = (Const *)root->parse->limitOffset;
        if (!off_const->constisnull) {
          if (off_const->consttype == INT8OID)
            off_val = DatumGetInt64(off_const->constvalue);
          else if (off_const->consttype == INT4OID)
            off_val = (int64)DatumGetInt32(off_const->constvalue);
        }
      } else {
        lim_val = -1;
      }
    }
    if (lim_val >= 0 && off_val >= 0) {
      fpinfo->pushed_limit = lim_val + off_val;
    }
  }

  double rows = 1000.0;
  int width = 64;

  MemoryContext type_io_mcxt = AllocSetContextCreate(
      CurrentMemoryContext, "pljs_fdw planner type io", ALLOCSET_SMALL_SIZES);
  FmgrInfo flinfo;
  memset(&flinfo, 0, sizeof(flinfo));
  flinfo.fn_oid = InvalidOid;
  flinfo.fn_mcxt = type_io_mcxt;
  pljs_encoding_init();
  pljs_type_io_cache *saved_types = pljs_type_io_enter(&flinfo);

  PG_TRY();
  {
    JSContext *ctx = pljs_fdw_get_context();
    JSValue wrapper = pljs_fdw_get_wrapper_instance(ctx, foreigntableid, &opts);

    JSValue ki_val = JS_GetPropertyStr(ctx, wrapper, "isKeyIndexed");
    if (JS_IsBool(ki_val)) {
      fpinfo->is_key_indexed = JS_ToBool(ctx, ki_val) != 0;
    }
    JS_FreeValue(ctx, ki_val);

    JSValue kc_val = JS_GetPropertyStr(ctx, wrapper, "keyColumn");
    if (JS_IsString(kc_val)) {
      const char *kc_str = JS_ToCString(ctx, kc_val);
      if (kc_str && kc_str[0] != '\0') {
        fpinfo->key_column = pstrdup(kc_str);
      }
      if (kc_str)
        JS_FreeCString(ctx, kc_str);
    }
    JS_FreeValue(ctx, kc_val);

    JSValue get_rel_size = JS_GetPropertyStr(ctx, wrapper, "getRelSize");
    if (JS_IsFunction(ctx, get_rel_size)) {
      JSValue plan_ctx = JS_NewObject(ctx);
      JS_SetPropertyStr(ctx, plan_ctx, "tableOid",
                        JS_NewUint32(ctx, (uint32_t)foreigntableid));

      JSValue quals_arr = JS_NewArray(ctx);
      for (int i = 0; i < fpinfo->pushed_quals_count; i++) {
        JS_SetPropertyUint32(ctx, quals_arr, (uint32_t)i,
                             pljs_fdw_qual_to_js(ctx, &fpinfo->pushed_quals[i],
                                                 NULL));
      }
      JS_SetPropertyStr(ctx, plan_ctx, "quals", quals_arr);
      if (fpinfo->pushed_limit >= 0) {
        JS_SetPropertyStr(ctx, plan_ctx, "limit",
                          JS_NewFloat64(ctx, (double)fpinfo->pushed_limit));
      }

      JSValue args[1] = {plan_ctx};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue res = JS_Call(ctx, get_rel_size, wrapper, 1, args);
      JS_FreeValue(ctx, plan_ctx);
      if (JS_IsException(res)) {
        JS_FreeValue(ctx, get_rel_size);
        JS_FreeValue(ctx, wrapper);
        pljs_ereport_js_exception(ctx);
      }
      if (JS_IsObject(res)) {
        JSValue r_val = JS_GetPropertyStr(ctx, res, "rows");
        if (JS_IsNumber(r_val)) {
          double d = 1000.0;
          JS_ToFloat64(ctx, &d, r_val);
          rows = d;
        }
        JS_FreeValue(ctx, r_val);

        JSValue w_val = JS_GetPropertyStr(ctx, res, "width");
        if (JS_IsNumber(w_val)) {
          int32_t w = 64;
          JS_ToInt32(ctx, &w, w_val);
          width = (int)w;
        }
        JS_FreeValue(ctx, w_val);
      }
      JS_FreeValue(ctx, res);
    }
    JS_FreeValue(ctx, get_rel_size);
    JS_FreeValue(ctx, wrapper);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
    MemoryContextDelete(type_io_mcxt);
  }
  PG_END_TRY();

  baserel->rows = clamp_row_est(rows);
  if (width > 0) {
    baserel->reltarget->width = width;
  }
  baserel->fdw_private = (void *)fpinfo;
}

static List *pljs_fdw_build_pathkeys(PlannerInfo *root, RelOptInfo *baserel,
                                     PljsFdwPlanState *fpinfo,
                                     JSContext *ctx, JSValue wrapper) {
  List *pathkeys = NIL;
  fpinfo->orderby_count = 0;
  fpinfo->orderby = NULL;

  JSValue get_pk = JS_GetPropertyStr(ctx, wrapper, "getPathKeys");
  if (!JS_IsFunction(ctx, get_pk)) {
    JS_FreeValue(ctx, get_pk);
    return NIL;
  }

  JSValue plan_ctx = JS_NewObject(ctx);
  JS_SetPropertyStr(ctx, plan_ctx, "tableOid",
                    JS_NewUint32(ctx, (uint32_t)fpinfo->foreigntableid));
  JSValue args[1] = {plan_ctx};
  JS_UpdateStackTop(JS_GetRuntime(ctx));
  JSValue pk_res = JS_Call(ctx, get_pk, wrapper, 1, args);
  JS_FreeValue(ctx, plan_ctx);
  JS_FreeValue(ctx, get_pk);

  if (JS_IsException(pk_res)) {
    JS_FreeValue(ctx, JS_GetException(ctx));
    return NIL;
  }
  if (!JS_IsArray(ctx, pk_res)) {
    JS_FreeValue(ctx, pk_res);
    return NIL;
  }

  int32_t len = pljs_js_array_length(pk_res, ctx);
  if (len <= 0) {
    JS_FreeValue(ctx, pk_res);
    return NIL;
  }

  fpinfo->orderby = (PljsOrderBy *)palloc0(sizeof(PljsOrderBy) * (size_t)len);

  Relation rel = table_open(fpinfo->foreigntableid, NoLock);
  TupleDesc tupdesc = RelationGetDescr(rel);

  for (int32_t i = 0; i < len; i++) {
    JSValue item = JS_GetPropertyUint32(ctx, pk_res, (uint32_t)i);
    if (!JS_IsObject(item)) {
      JS_FreeValue(ctx, item);
      continue;
    }

    JSValue col_v = JS_GetPropertyStr(ctx, item, "column");
    if (!JS_IsString(col_v)) {
      JS_FreeValue(ctx, col_v);
      JS_FreeValue(ctx, item);
      continue;
    }
    const char *cname_cstr = JS_ToCString(ctx, col_v);
    char *cname = cname_cstr ? pstrdup(cname_cstr) : NULL;
    if (cname_cstr)
      JS_FreeCString(ctx, cname_cstr);
    JS_FreeValue(ctx, col_v);

    bool asc = true;
    JSValue asc_v = JS_GetPropertyStr(ctx, item, "ascending");
    if (JS_IsBool(asc_v))
      asc = JS_ToBool(ctx, asc_v) != 0;
    JS_FreeValue(ctx, asc_v);

    bool nulls_first = !asc;
    JSValue nf_v = JS_GetPropertyStr(ctx, item, "nullsFirst");
    if (JS_IsBool(nf_v))
      nulls_first = JS_ToBool(ctx, nf_v) != 0;
    JS_FreeValue(ctx, nf_v);
    JS_FreeValue(ctx, item);

    if (!cname)
      continue;

    Form_pg_attribute matched_attr = NULL;
    for (int a = 0; a < tupdesc->natts; a++) {
      Form_pg_attribute attr = TupleDescAttr(tupdesc, a);
      if (!attr->attisdropped && strcmp(NameStr(attr->attname), cname) == 0) {
        matched_attr = attr;
        break;
      }
    }
    if (!matched_attr)
      continue;

    Oid sort_op = InvalidOid;
    get_sort_group_operators(matched_attr->atttypid, true, false, false,
                             &sort_op, NULL, NULL, NULL);
    if (!OidIsValid(sort_op))
      continue;

    if (!asc) {
      Oid comm_op = get_commutator(sort_op);
      if (OidIsValid(comm_op))
        sort_op = comm_op;
    }

    Var *var = makeVar(baserel->relid, matched_attr->attnum,
                       matched_attr->atttypid, matched_attr->atttypmod,
                       matched_attr->attcollation, 0);
    List *expr_pks = build_expression_pathkey(root, (Expr *)var, sort_op,
                                              baserel->relids, true);
    if (expr_pks != NIL) {
      pathkeys = list_concat(pathkeys, expr_pks);
      PljsOrderBy *ob = &fpinfo->orderby[fpinfo->orderby_count++];
      ob->colname = cname;
      ob->ascending = asc;
      ob->nulls_first = nulls_first;
    }
  }

  table_close(rel, NoLock);
  JS_FreeValue(ctx, pk_res);
  return pathkeys;
}

static void pljs_fdw_get_foreign_paths(PlannerInfo *root, RelOptInfo *baserel,
                                       Oid foreigntableid) {
  PljsFdwPlanState *fpinfo = (PljsFdwPlanState *)baserel->fdw_private;
  volatile Cost startup_cost = 10.0;
  volatile Cost total_cost = startup_cost + baserel->rows * 0.1;
  List * volatile pathkeys = NIL;

  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);

  MemoryContext type_io_mcxt = AllocSetContextCreate(
      CurrentMemoryContext, "pljs_fdw paths type io", ALLOCSET_SMALL_SIZES);
  FmgrInfo flinfo;
  memset(&flinfo, 0, sizeof(flinfo));
  flinfo.fn_oid = InvalidOid;
  flinfo.fn_mcxt = type_io_mcxt;
  pljs_encoding_init();
  pljs_type_io_cache *saved_types = pljs_type_io_enter(&flinfo);

  PG_TRY();
  {
    JSContext *ctx = pljs_fdw_get_context();
    JSValue wrapper = pljs_fdw_get_wrapper_instance(ctx, foreigntableid, &opts);

    JSValue get_rel_size = JS_GetPropertyStr(ctx, wrapper, "getRelSize");
    if (JS_IsFunction(ctx, get_rel_size)) {
      JSValue plan_ctx = JS_NewObject(ctx);
      JS_SetPropertyStr(ctx, plan_ctx, "tableOid",
                        JS_NewUint32(ctx, (uint32_t)foreigntableid));
      JSValue quals_arr = JS_NewArray(ctx);
      if (fpinfo) {
        for (int i = 0; i < fpinfo->pushed_quals_count; i++) {
          JS_SetPropertyUint32(ctx, quals_arr, (uint32_t)i,
                               pljs_fdw_qual_to_js(ctx, &fpinfo->pushed_quals[i],
                                                   NULL));
        }
      }
      JS_SetPropertyStr(ctx, plan_ctx, "quals", quals_arr);
      if (fpinfo && fpinfo->pushed_limit >= 0) {
        JS_SetPropertyStr(ctx, plan_ctx, "limit",
                          JS_NewFloat64(ctx, (double)fpinfo->pushed_limit));
      }

      JSValue args[1] = {plan_ctx};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue res = JS_Call(ctx, get_rel_size, wrapper, 1, args);
      JS_FreeValue(ctx, plan_ctx);
      if (JS_IsException(res)) {
        JS_FreeValue(ctx, get_rel_size);
        JS_FreeValue(ctx, wrapper);
        pljs_ereport_js_exception(ctx);
      }
      if (JS_IsObject(res)) {
        JSValue sc_val = JS_GetPropertyStr(ctx, res, "startupCost");
        if (JS_IsNumber(sc_val)) {
          double d = 10.0;
          JS_ToFloat64(ctx, &d, sc_val);
          startup_cost = d;
        }
        JS_FreeValue(ctx, sc_val);

        JSValue tc_val = JS_GetPropertyStr(ctx, res, "totalCost");
        if (JS_IsNumber(tc_val)) {
          double d = total_cost;
          JS_ToFloat64(ctx, &d, tc_val);
          total_cost = d;
        }
        JS_FreeValue(ctx, tc_val);
      }
      JS_FreeValue(ctx, res);
    }
    JS_FreeValue(ctx, get_rel_size);

    if (fpinfo) {
      pathkeys = pljs_fdw_build_pathkeys(root, baserel, fpinfo, ctx, wrapper);
    }
    JS_FreeValue(ctx, wrapper);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
    MemoryContextDelete(type_io_mcxt);
  }
  PG_END_TRY();

  add_path(baserel, (Path *)
#if PG_VERSION_NUM >= 180000
           create_foreignscan_path(
               root, baserel, NULL, baserel->rows, 0, startup_cost, total_cost,
               pathkeys, NULL, NULL,
#if PG_VERSION_NUM >= 170000
               NIL,
#endif
               pathkeys != NIL ? list_make1(makeInteger(1)) : NIL)
#else
           create_foreignscan_path(
               root, baserel, NULL, baserel->rows, startup_cost, total_cost,
               pathkeys, NULL, NULL,
#if PG_VERSION_NUM >= 170000
               NIL,
#endif
               pathkeys != NIL ? list_make1(makeInteger(1)) : NIL)
#endif
  );

  if (baserel->joininfo != NIL) {
    Relation rel = table_open(foreigntableid, NoLock);
    TupleDesc tupdesc = RelationGetDescr(rel);

    ListCell *lc;
    foreach (lc, baserel->joininfo) {
      RestrictInfo *rinfo = (RestrictInfo *)lfirst(lc);
      if (rinfo->mergeopfamilies == NIL && !rinfo->can_join)
        continue;

      PljsQual q;
      if (!pljs_fdw_extract_qual((Node *)rinfo->clause, baserel->relid, tupdesc,
                                 &q))
        continue;

      Relids req_outer = bms_difference(rinfo->clause_relids, baserel->relids);
      if (bms_is_empty(req_outer))
        continue;

      ParamPathInfo *param_info = get_baserel_parampathinfo(root, baserel, req_outer);
      if (!param_info)
        continue;

      double param_rows =
          (fpinfo && fpinfo->is_key_indexed &&
           strcmp(q.colname, fpinfo->key_column) == 0 &&
           strcmp(q.opname, "=") == 0)
              ? 1.0
              : clamp_row_est(baserel->rows * 0.1);
      Cost param_startup = 0.2;
      Cost param_total = param_startup + param_rows * 0.05;

      add_path(baserel, (Path *)
#if PG_VERSION_NUM >= 180000
               create_foreignscan_path(root, baserel, NULL, param_rows, 0,
                                       param_startup, param_total, NIL,
                                       param_info->ppi_req_outer, NULL,
#if PG_VERSION_NUM >= 170000
                                       NIL,
#endif
                                       NIL)
#else
               create_foreignscan_path(root, baserel, NULL, param_rows,
                                       param_startup, param_total, NIL,
                                       param_info->ppi_req_outer, NULL,
#if PG_VERSION_NUM >= 170000
                                       NIL,
#endif
                                       NIL)
#endif
      );
    }

    table_close(rel, NoLock);
  }
}

static ForeignScan *pljs_fdw_get_foreign_plan(PlannerInfo *root,
                                              RelOptInfo *baserel,
                                              Oid foreigntableid,
                                              ForeignPath *best_path,
                                              List *tlist, List *scan_clauses,
                                              Plan *outer_plan) {
  Index scan_relid = baserel->relid;
  PljsFdwPlanState *fpinfo = (PljsFdwPlanState *)baserel->fdw_private;

  Relation rel = table_open(foreigntableid, NoLock);
  TupleDesc tupdesc = RelationGetDescr(rel);

  List *local_exprs = NIL;
  List *fdw_exprs = NIL;

  ListCell *lc;
  foreach (lc, scan_clauses) {
    RestrictInfo *rinfo = (RestrictInfo *)lfirst(lc);
    if (rinfo->pseudoconstant) {
      local_exprs = lappend(local_exprs, rinfo->clause);
      continue;
    }

    PljsQual q;
    if (pljs_fdw_extract_qual((Node *)rinfo->clause, scan_relid, tupdesc, &q)) {
      fdw_exprs = lappend(fdw_exprs, rinfo->clause);
      if (fpinfo && fpinfo->is_key_indexed &&
          strcmp(q.colname, fpinfo->key_column) == 0 &&
          (strcmp(q.opname, "=") == 0 || strcmp(q.opname, "IN") == 0)) {
        continue;
      }
      if (!q.is_param) {
        continue;
      }
    }
    local_exprs = lappend(local_exprs, rinfo->clause);
  }

  table_close(rel, NoLock);

  int64 pushed_lim = (fpinfo != NULL) ? fpinfo->pushed_limit : -1;
  if (pushed_lim < 0) {
    if (root->limit_tuples > 0.0 && root->limit_tuples < 1e12) {
      pushed_lim = (int64)ceil(root->limit_tuples);
    } else if (root->parse && root->parse->limitCount &&
               IsA(root->parse->limitCount, Const) &&
               !((Const *)root->parse->limitCount)->constisnull) {
      Const *lc_const = (Const *)root->parse->limitCount;
      pushed_lim = (lc_const->consttype == INT4OID)
                       ? (int64)DatumGetInt32(lc_const->constvalue)
                       : DatumGetInt64(lc_const->constvalue);
      if (root->parse->limitOffset && IsA(root->parse->limitOffset, Const) &&
          !((Const *)root->parse->limitOffset)->constisnull) {
        Const *lo_const = (Const *)root->parse->limitOffset;
        pushed_lim += (lo_const->consttype == INT4OID)
                          ? (int64)DatumGetInt32(lo_const->constvalue)
                          : DatumGetInt64(lo_const->constvalue);
      }
    }
  }

  bool has_sort_needed = false;
  if (root->sort_pathkeys != NIL) {
    if (!best_path->path.pathkeys ||
        !pathkeys_contained_in(root->sort_pathkeys, best_path->path.pathkeys)) {
      has_sort_needed = true;
    }
  }
  if (has_sort_needed || local_exprs != NIL) {
    pushed_lim = -1;
  }

  List *fdw_private = list_make1(makeInteger((int)pushed_lim));
  if (best_path->fdw_private != NIL && fpinfo != NULL &&
      fpinfo->orderby_count > 0) {
    List *ob_list = NIL;
    for (int i = 0; i < fpinfo->orderby_count; i++) {
      PljsOrderBy *ob = &fpinfo->orderby[i];
      List *item = list_make3(makeString(pstrdup(ob->colname)),
                              makeInteger(ob->ascending ? 1 : 0),
                              makeInteger(ob->nulls_first ? 1 : 0));
      ob_list = lappend(ob_list, item);
    }
    fdw_private = lappend(fdw_private, ob_list);
  }

  return make_foreignscan(tlist, local_exprs, scan_relid, fdw_exprs,
                          fdw_private, NIL, NIL, outer_plan);
}

/*
 * ---------- FDW Executor Scan Callbacks ----------
 */

static void pljs_fdw_begin_foreign_scan(ForeignScanState *node, int eflags) {
  if (eflags & EXEC_FLAG_EXPLAIN_ONLY) {
    node->fdw_state = NULL;
    return;
  }

  Relation rel = node->ss.ss_currentRelation;
  Oid foreigntableid = RelationGetRelid(rel);
  ForeignScan *fsplan = (ForeignScan *)node->ss.ps.plan;
  EState *estate = node->ss.ps.state;

  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);

  MemoryContext scan_mcxt = AllocSetContextCreate(
      estate->es_query_cxt, "pljs_fdw scan state", ALLOCSET_DEFAULT_SIZES);
  MemoryContext row_cxt = AllocSetContextCreate(
      scan_mcxt, "pljs_fdw row conversion", ALLOCSET_DEFAULT_SIZES);

  MemoryContext oldcxt = MemoryContextSwitchTo(scan_mcxt);

  PljsFdwScanState *festate =
      (PljsFdwScanState *)palloc0(sizeof(PljsFdwScanState));
  festate->user_id = GetUserId();
  festate->scan_mcxt = scan_mcxt;
  festate->row_cxt = row_cxt;
  festate->foreigntableid = foreigntableid;
  festate->is_key_indexed = false;
  festate->key_column = pstrdup("key");
  festate->rowid_column = pstrdup("id");
  festate->rowid_attno = InvalidAttrNumber;
  festate->pushed_limit = -1;
  festate->emitted_rows = 0;
  festate->cache_results = true;
  festate->cache_max_entries = 64;
  festate->cache_max_bytes = 16LL * 1024LL * 1024LL;
  festate->wrapper_instance = JS_UNDEFINED;
  festate->iter_or_array = JS_UNDEFINED;

  festate->cleanup_cb.func = pljs_fdw_scan_cleanup_cb;
  festate->cleanup_cb.arg = festate;
  MemoryContextRegisterResetCallback(scan_mcxt, &festate->cleanup_cb);

  festate->type_io_flinfo.fn_oid = InvalidOid;
  festate->type_io_flinfo.fn_mcxt = scan_mcxt;

  const char *opt_cr = pljs_fdw_opt_get(&opts, "cache_results");
  if (opt_cr && (strcmp(opt_cr, "false") == 0 || strcmp(opt_cr, "off") == 0 ||
                 strcmp(opt_cr, "0") == 0)) {
    festate->cache_results = false;
  }
  const char *opt_cs = pljs_fdw_opt_get(&opts, "cache_size");
  if (opt_cs) {
    int cs = atoi(opt_cs);
    if (cs > 0)
      festate->cache_max_entries = cs;
  }
  const char *opt_cm = pljs_fdw_opt_get(&opts, "cache_memory_limit");
  if (opt_cm) {
    long long cm = atoll(opt_cm);
    if (cm > 0)
      festate->cache_max_bytes = (int64)cm;
  }
  const char *opt_rc = pljs_fdw_opt_get(&opts, "rowid_column");
  if (opt_rc && opt_rc[0] != '\0') {
    festate->rowid_column = pstrdup(opt_rc);
    festate->key_column = pstrdup(opt_rc);
  }
  const char *opt_pk = pljs_fdw_opt_get(&opts, "pk");
  if (opt_pk && opt_pk[0] != '\0') {
    festate->key_column = pstrdup(opt_pk);
    if (!opt_rc) {
      festate->rowid_column = pstrdup(opt_pk);
    }
  }
  const char *opt_key = pljs_fdw_opt_get(&opts, "key");
  if (opt_key && opt_key[0] != '\0') {
    festate->key_column = pstrdup(opt_key);
    if (!opt_rc && !opt_pk) {
      festate->rowid_column = pstrdup(opt_key);
    }
  }

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&festate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = pljs_fdw_get_context();
    festate->ctx = ctx;
    festate->wrapper_instance =
        pljs_fdw_get_wrapper_instance(ctx, foreigntableid, &opts);

    JSValue ki_val =
        JS_GetPropertyStr(ctx, festate->wrapper_instance, "isKeyIndexed");
    if (JS_IsBool(ki_val)) {
      festate->is_key_indexed = JS_ToBool(ctx, ki_val) != 0;
    }
    JS_FreeValue(ctx, ki_val);

    JSValue kc_val =
        JS_GetPropertyStr(ctx, festate->wrapper_instance, "keyColumn");
    if (JS_IsString(kc_val)) {
      const char *kc_str = JS_ToCString(ctx, kc_val);
      if (kc_str && kc_str[0] != '\0') {
        festate->key_column = pstrdup(kc_str);
      }
      if (kc_str)
        JS_FreeCString(ctx, kc_str);
    }
    JS_FreeValue(ctx, kc_val);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  TupleDesc tupdesc = RelationGetDescr(rel);
  festate->proj_cols = (char **)palloc0(sizeof(char *) * (size_t)tupdesc->natts);
  Bitmapset *attrs_used = NULL;
  if (node->ss.ps.plan->targetlist != NIL) {
    ListCell *tlc;
    foreach (tlc, node->ss.ps.plan->targetlist) {
      TargetEntry *tle = (TargetEntry *)lfirst(tlc);
      pull_varattnos((Node *)tle->expr, fsplan->scan.scanrelid, &attrs_used);
      if (tle->resjunk && tle->resname &&
          strcmp(tle->resname, "__pljs_rowid") == 0) {
        festate->rowid_attno = tle->resno;
      }
    }
  }
  if (node->ss.ps.plan->qual != NIL) {
    pull_varattnos((Node *)node->ss.ps.plan->qual, fsplan->scan.scanrelid,
                   &attrs_used);
  }
  for (int i = 0; i < tupdesc->natts; i++) {
    Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
    if (!attr->attisdropped) {
      if (attrs_used != NULL &&
          (bms_is_member(0 - FirstLowInvalidHeapAttributeNumber, attrs_used) ||
           bms_is_member(attr->attnum - FirstLowInvalidHeapAttributeNumber,
                         attrs_used))) {
        festate->proj_cols[festate->proj_cols_count++] =
            pstrdup(NameStr(attr->attname));
      }
    }
  }
  bms_free(attrs_used);

  int n_fdw_exprs = list_length(fsplan->fdw_exprs);
  if (n_fdw_exprs > 0) {
    festate->quals = (PljsQual *)palloc0(sizeof(PljsQual) * (size_t)n_fdw_exprs);
  }
  ListCell *lc;
  foreach (lc, fsplan->fdw_exprs) {
    Expr *clause = (Expr *)lfirst(lc);
    PljsQual q;
    if (pljs_fdw_extract_qual((Node *)clause, fsplan->scan.scanrelid, tupdesc,
                              &q)) {
      if (q.is_param && q.right_expr != NULL) {
        q.expr_state = ExecInitExpr(q.right_expr, (PlanState *)node);
      }
      festate->quals[festate->quals_count++] = q;
    }
  }

  if (fsplan->fdw_private != NIL) {
    if (list_length(fsplan->fdw_private) >= 1) {
      Node *lim_node = (Node *)linitial(fsplan->fdw_private);
      if (lim_node && IsA(lim_node, Integer)) {
        festate->pushed_limit = (int64)intVal(lim_node);
      }
    }
    if (list_length(fsplan->fdw_private) >= 2) {
      List *ob_list = (List *)lsecond(fsplan->fdw_private);
      int n_ob = list_length(ob_list);
      if (n_ob > 0) {
        festate->orderby =
            (PljsOrderBy *)palloc0(sizeof(PljsOrderBy) * (size_t)n_ob);
      }
      ListCell *oblc;
      foreach (oblc, ob_list) {
        List *item = (List *)lfirst(oblc);
        if (list_length(item) == 3) {
          PljsOrderBy *ob = &festate->orderby[festate->orderby_count++];
          ob->colname = pstrdup(strVal(linitial(item)));
          ob->ascending = (intVal(lsecond(item)) != 0);
          ob->nulls_first = (intVal(lthird(item)) != 0);
        }
      }
    }
  }

  MemoryContextSwitchTo(oldcxt);
  node->fdw_state = (void *)festate;
}

static char *pljs_fdw_build_param_cache_key(PljsFdwScanState *festate,
                                            ExprContext *econtext) {
  StringInfoData buf;
  initStringInfo(&buf);
  for (int i = 0; i < festate->quals_count; i++) {
    const PljsQual *q = &festate->quals[i];
    if (!q->is_param)
      continue;
    appendStringInfo(&buf, "%s:%s=", q->colname, q->opname);
    bool isnull = true;
    Datum val = 0;
    if (q->expr_state && econtext) {
      val = ExecEvalExpr(q->expr_state, econtext, &isnull);
    }
    if (isnull) {
      appendStringInfoString(&buf, "<NULL>;");
    } else {
      Oid typoutput = InvalidOid;
      bool typIsVarlena = false;
      getTypeOutputInfo(q->const_type, &typoutput, &typIsVarlena);
      char *str = OidOutputFunctionCall(typoutput, val);
      appendStringInfo(&buf, "%s;", str ? str : "");
      if (str)
        pfree(str);
    }
  }
  return buf.data;
}

static bool pljs_fdw_has_param_quals(PljsFdwScanState *festate) {
  for (int i = 0; i < festate->quals_count; i++) {
    if (festate->quals[i].is_param)
      return true;
  }
  return false;
}

static JSValue pljs_fdw_build_scan_request(JSContext *ctx,
                                           PljsFdwScanState *festate,
                                           ExprContext *econtext,
                                           JSValue *out_keys,
                                           bool *out_use_lookup) {
  JSValue req = JS_NewObject(ctx);
  JS_SetPropertyStr(ctx, req, "tableOid",
                    JS_NewUint32(ctx, (uint32_t)festate->foreigntableid));

  JSValue cols_arr = JS_NewArray(ctx);
  for (int i = 0; i < festate->proj_cols_count; i++) {
    JS_SetPropertyUint32(ctx, cols_arr, (uint32_t)i,
                         JS_NewString(ctx, festate->proj_cols[i]));
  }
  JS_SetPropertyStr(ctx, req, "columns", cols_arr);

  JSValue filters_arr = JS_NewArray(ctx);
  JSValue keys_arr = JS_NewArray(ctx);
  uint32_t f_idx = 0;
  uint32_t k_idx = 0;

  for (int i = 0; i < festate->quals_count; i++) {
    const PljsQual *q = &festate->quals[i];
    JSValue q_js = pljs_fdw_qual_to_js(ctx, q, econtext);

    if (festate->is_key_indexed &&
        strcmp(q->colname, festate->key_column) == 0 &&
        (strcmp(q->opname, "=") == 0 || strcmp(q->opname, "IN") == 0)) {
      JSValue val_v = JS_GetPropertyStr(ctx, q_js, "value");
      if (!JS_IsNull(val_v) && !JS_IsUndefined(val_v)) {
        if (strcmp(q->opname, "=") == 0) {
          JS_SetPropertyUint32(ctx, keys_arr, k_idx++, val_v);
        } else if (JS_IsArray(ctx, val_v)) {
          int32_t alen = pljs_js_array_length(val_v, ctx);
          for (int32_t a = 0; a < alen; a++) {
            JSValue elem = JS_GetPropertyUint32(ctx, val_v, (uint32_t)a);
            if (!JS_IsNull(elem) && !JS_IsUndefined(elem)) {
              JS_SetPropertyUint32(ctx, keys_arr, k_idx++, elem);
            } else {
              JS_FreeValue(ctx, elem);
            }
          }
          JS_FreeValue(ctx, val_v);
        } else {
          JS_FreeValue(ctx, val_v);
        }
      } else {
        JS_FreeValue(ctx, val_v);
      }
      JS_FreeValue(ctx, q_js);
      continue;
    }

    JS_SetPropertyUint32(ctx, filters_arr, f_idx++, q_js);
  }

  JS_SetPropertyStr(ctx, req, "filters", filters_arr);
  JS_SetPropertyStr(ctx, req, "keys", JS_DupValue(ctx, keys_arr));
  JS_SetPropertyStr(ctx, req, "isKeyIndexed",
                    JS_NewBool(ctx, festate->is_key_indexed));

  JSValue ob_arr = JS_NewArray(ctx);
  for (int i = 0; i < festate->orderby_count; i++) {
    JSValue ob_item = JS_NewObject(ctx);
    JS_SetPropertyStr(ctx, ob_item, "column",
                      JS_NewString(ctx, festate->orderby[i].colname));
    JS_SetPropertyStr(ctx, ob_item, "ascending",
                      JS_NewBool(ctx, festate->orderby[i].ascending));
    JS_SetPropertyStr(ctx, ob_item, "nullsFirst",
                      JS_NewBool(ctx, festate->orderby[i].nulls_first));
    JS_SetPropertyUint32(ctx, ob_arr, (uint32_t)i, ob_item);
  }
  JS_SetPropertyStr(ctx, req, "orderBy", ob_arr);

  if (festate->pushed_limit >= 0) {
    JS_SetPropertyStr(ctx, req, "limit",
                      JS_NewFloat64(ctx, (double)festate->pushed_limit));
  }

  *out_keys = keys_arr;
  *out_use_lookup = (festate->is_key_indexed && k_idx > 0);
  return req;
}

static void pljs_fdw_start_js_scan(JSContext *ctx, PljsFdwScanState *festate,
                                   ExprContext *econtext) {
  if (!JS_IsUndefined(festate->iter_or_array)) {
    JS_FreeValue(ctx, festate->iter_or_array);
    festate->iter_or_array = JS_UNDEFINED;
  }

  festate->scan_started = true;
  festate->eof_reached = false;
  festate->row_idx = 0;
  festate->row_count = 0;
  festate->emitted_rows = 0;
  festate->is_generator = false;
  festate->is_array = false;
  festate->is_func = false;

  JSValue keys_arr = JS_UNDEFINED;
  bool use_lookup = false;
  JSValue req =
      pljs_fdw_build_scan_request(ctx, festate, econtext, &keys_arr, &use_lookup);

  JSValue wrapper = festate->wrapper_instance;
  JSValue result_val = JS_UNDEFINED;

  if (use_lookup) {
    int32_t klen = pljs_js_array_length(keys_arr, ctx);
    if (klen == 1) {
      JSValue lk_fn = JS_GetPropertyStr(ctx, wrapper, "lookupKey");
      if (JS_IsFunction(ctx, lk_fn)) {
        JSValue k0 = JS_GetPropertyUint32(ctx, keys_arr, 0);
        JSValue args[2] = {k0, req};
        JS_UpdateStackTop(JS_GetRuntime(ctx));
        result_val = JS_Call(ctx, lk_fn, wrapper, 2, args);
        JS_FreeValue(ctx, k0);
        JS_FreeValue(ctx, lk_fn);
        JS_FreeValue(ctx, keys_arr);
        JS_FreeValue(ctx, req);
        if (JS_IsException(result_val)) {
          pljs_ereport_js_exception(ctx);
        }
      } else {
        JS_FreeValue(ctx, lk_fn);
      }
    } else if (klen > 1) {
      JSValue lks_fn = JS_GetPropertyStr(ctx, wrapper, "lookupKeys");
      if (JS_IsFunction(ctx, lks_fn)) {
        JSValue args[2] = {keys_arr, req};
        JS_UpdateStackTop(JS_GetRuntime(ctx));
        result_val = JS_Call(ctx, lks_fn, wrapper, 2, args);
        JS_FreeValue(ctx, lks_fn);
        JS_FreeValue(ctx, keys_arr);
        JS_FreeValue(ctx, req);
        if (JS_IsException(result_val)) {
          pljs_ereport_js_exception(ctx);
        }
      } else {
        JS_FreeValue(ctx, lks_fn);
      }
    }
  }

  if (JS_IsUndefined(result_val)) {
    JS_FreeValue(ctx, keys_arr);
    JSValue scan_fn = JS_GetPropertyStr(ctx, wrapper, "scan");
    if (!JS_IsFunction(ctx, scan_fn)) {
      JS_FreeValue(ctx, scan_fn);
      JS_FreeValue(ctx, req);
      festate->eof_reached = true;
      return;
    }
    JSValue args[1] = {req};
    JS_UpdateStackTop(JS_GetRuntime(ctx));
    result_val = JS_Call(ctx, scan_fn, wrapper, 1, args);
    JS_FreeValue(ctx, scan_fn);
    JS_FreeValue(ctx, req);
    if (JS_IsException(result_val)) {
      pljs_ereport_js_exception(ctx);
    }
  }

  if (JS_IsUndefined(result_val) || JS_IsNull(result_val)) {
    JS_FreeValue(ctx, result_val);
    festate->eof_reached = true;
    return;
  }

  if (JS_IsArray(ctx, result_val)) {
    festate->is_array = true;
    festate->row_count = (uint32_t)pljs_js_array_length(result_val, ctx);
    festate->iter_or_array = result_val;
    if (festate->row_count == 0)
      festate->eof_reached = true;
    return;
  }

  if (JS_IsFunction(ctx, result_val)) {
    festate->is_func = true;
    festate->iter_or_array = result_val;
    return;
  }

  if (JS_IsObject(result_val)) {
    JSValue next_fn = JS_GetPropertyStr(ctx, result_val, "next");
    if (JS_IsFunction(ctx, next_fn)) {
      JS_FreeValue(ctx, next_fn);
      festate->is_generator = true;
      festate->iter_or_array = result_val;
      return;
    }
    JS_FreeValue(ctx, next_fn);

    festate->iter_or_array = result_val;
    festate->row_count = 1;
    return;
  }

  JS_FreeValue(ctx, result_val);
  festate->eof_reached = true;
}

static void pljs_fdw_row_to_slot(JSContext *ctx, JSValue row,
                                 TupleTableSlot *slot,
                                 PljsFdwScanState *festate) {
  (void)festate;
  ExecClearTuple(slot);
  TupleDesc tupdesc = slot->tts_tupleDescriptor;
  int natts = tupdesc->natts;

  for (int i = 0; i < natts; i++) {
    slot->tts_isnull[i] = true;
    slot->tts_values[i] = (Datum)0;
  }

  if (JS_IsArray(ctx, row)) {
    for (int i = 0; i < natts; i++) {
      Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
      if (attr->attisdropped)
        continue;

      JSValue val = JS_GetPropertyUint32(ctx, row, (uint32_t)i);
      if (JS_IsException(val)) {
        pljs_ereport_js_exception(ctx);
      }
      if (!JS_IsUndefined(val) && !JS_IsNull(val)) {
        bool isnull = false;
        Datum d = pljs_jsvalue_to_datum_typmod_free(
            attr->atttypid, attr->atttypmod, val, &isnull, ctx);
        slot->tts_values[i] = d;
        slot->tts_isnull[i] = isnull;
      } else {
        JS_FreeValue(ctx, val);
      }
    }
  } else if (JS_IsObject(row)) {
    for (int i = 0; i < natts; i++) {
      Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
      if (attr->attisdropped)
        continue;

      JSValue val = JS_GetPropertyStr(ctx, row, NameStr(attr->attname));
      if (JS_IsException(val)) {
        pljs_ereport_js_exception(ctx);
      }
      if (!JS_IsUndefined(val) && !JS_IsNull(val)) {
        bool isnull = false;
        Datum d = pljs_jsvalue_to_datum_typmod_free(
            attr->atttypid, attr->atttypmod, val, &isnull, ctx);
        slot->tts_values[i] = d;
        slot->tts_isnull[i] = isnull;
      } else {
        JS_FreeValue(ctx, val);
      }
    }
  }

  ExecStoreVirtualTuple(slot);
}

static void pljs_fdw_lru_move_to_front(PljsFdwScanState *festate,
                                       PljsCacheEntry *entry) {
  if (festate->lru_head == entry)
    return;
  if (entry->prev)
    entry->prev->next = entry->next;
  if (entry->next)
    entry->next->prev = entry->prev;
  if (festate->lru_tail == entry)
    festate->lru_tail = entry->prev;

  entry->prev = NULL;
  entry->next = festate->lru_head;
  if (festate->lru_head)
    festate->lru_head->prev = entry;
  festate->lru_head = entry;
  if (!festate->lru_tail)
    festate->lru_tail = entry;
}

static PljsCacheEntry *pljs_fdw_lru_find(PljsFdwScanState *festate,
                                         const char *key) {
  for (PljsCacheEntry *curr = festate->lru_head; curr != NULL;
       curr = curr->next) {
    if (strcmp(curr->key, key) == 0) {
      return curr;
    }
  }
  return NULL;
}

static PljsCacheEntry *pljs_fdw_lru_insert(PljsFdwScanState *festate,
                                           const char *key,
                                           Tuplestorestate *store) {
  while ((festate->cache_entry_count >= festate->cache_max_entries ||
          festate->cache_current_bytes >= festate->cache_max_bytes) &&
         festate->lru_tail != NULL &&
         festate->lru_tail != festate->active_cache_entry) {
    PljsCacheEntry *victim = festate->lru_tail;
    festate->lru_tail = victim->prev;
    if (festate->lru_tail)
      festate->lru_tail->next = NULL;
    else
      festate->lru_head = NULL;

    if (victim->store && victim->store != festate->tuplestore) {
      tuplestore_end(victim->store);
      victim->store = NULL;
    }
    festate->cache_current_bytes -= victim->bytes;
    if (festate->cache_current_bytes < 0)
      festate->cache_current_bytes = 0;
    festate->cache_entry_count--;
  }

  MemoryContext oldcxt = MemoryContextSwitchTo(festate->scan_mcxt);
  PljsCacheEntry *entry =
      (PljsCacheEntry *)palloc0(sizeof(PljsCacheEntry));
  entry->key = pstrdup(key);
  entry->store = store;
  entry->complete = false;
  entry->bytes = 1024;
  MemoryContextSwitchTo(oldcxt);

  entry->prev = NULL;
  entry->next = festate->lru_head;
  if (festate->lru_head)
    festate->lru_head->prev = entry;
  festate->lru_head = entry;
  if (!festate->lru_tail)
    festate->lru_tail = entry;
  festate->cache_entry_count++;
  festate->cache_current_bytes += entry->bytes;
  return entry;
}

static TupleTableSlot *pljs_fdw_iterate_foreign_scan(ForeignScanState *node) {
  PljsFdwScanState *festate = (PljsFdwScanState *)node->fdw_state;
  TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;
  if (!festate)
    return ExecClearTuple(slot);

  if (festate->reading_from_tuplestore && festate->tuplestore != NULL) {
    if (festate->pushed_limit >= 0 &&
        festate->emitted_rows >= festate->pushed_limit) {
      return ExecClearTuple(slot);
    }
    if (tuplestore_gettupleslot(festate->tuplestore, true, false, slot)) {
      festate->emitted_rows++;
      return slot;
    }
    return ExecClearTuple(slot);
  }

  if (festate->eof_reached) {
    return ExecClearTuple(slot);
  }

  if (festate->pushed_limit >= 0 &&
      festate->emitted_rows >= festate->pushed_limit) {
    festate->eof_reached = true;
    if (festate->active_cache_entry != NULL) {
      festate->active_cache_entry->complete = true;
    }
    return ExecClearTuple(slot);
  }

  MemoryContextReset(festate->row_cxt);
  MemoryContext oldcxt = MemoryContextSwitchTo(festate->row_cxt);

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&festate->type_io_flinfo);

  TupleTableSlot *ret_slot = NULL;

  PG_TRY();
  {
    JSContext *ctx = festate->ctx;
    ExprContext *econtext = node->ss.ps.ps_ExprContext;

    if (!festate->scan_started) {
      if (festate->cache_results && pljs_fdw_has_param_quals(festate) &&
          festate->active_cache_entry == NULL) {
        char *param_key = pljs_fdw_build_param_cache_key(festate, econtext);
        PljsCacheEntry *found = pljs_fdw_lru_find(festate, param_key);
        if (found != NULL && found->complete && found->store != NULL) {
          pljs_fdw_lru_move_to_front(festate, found);
          festate->active_cache_entry = found;
          festate->tuplestore = found->store;
          tuplestore_rescan(festate->tuplestore);
          festate->reading_from_tuplestore = true;
          festate->emitted_rows = 0;
          festate->stats_cache_hits++;
          pfree(param_key);
          if (tuplestore_gettupleslot(festate->tuplestore, true, false, slot)) {
            festate->emitted_rows++;
            ret_slot = slot;
          } else {
            ret_slot = ExecClearTuple(slot);
          }
        } else {
          MemoryContext ts_old = MemoryContextSwitchTo(festate->scan_mcxt);
          Tuplestorestate *new_store =
              tuplestore_begin_heap(true, false, work_mem);
          MemoryContextSwitchTo(ts_old);
          if (found != NULL) {
            if (found->store != NULL) {
              tuplestore_end(found->store);
            }
            found->store = new_store;
            found->complete = false;
            pljs_fdw_lru_move_to_front(festate, found);
            festate->active_cache_entry = found;
          } else {
            festate->active_cache_entry =
                pljs_fdw_lru_insert(festate, param_key, new_store);
          }
          festate->tuplestore = new_store;
          pfree(param_key);
        }
      } else if (festate->cache_results && festate->tuplestore == NULL) {
        MemoryContext ts_old = MemoryContextSwitchTo(festate->scan_mcxt);
        festate->tuplestore = tuplestore_begin_heap(true, false, work_mem);
        MemoryContextSwitchTo(ts_old);
      }

      if (ret_slot == NULL) {
        festate->stats_cache_misses++;
        pljs_fdw_start_js_scan(ctx, festate, econtext);
        if (festate->eof_reached) {
          if (festate->active_cache_entry != NULL) {
            festate->active_cache_entry->complete = true;
          }
          ret_slot = ExecClearTuple(slot);
        }
      }
    }

    if (ret_slot == NULL) {
      JSValue source = festate->iter_or_array;
      JSValue row_val = JS_UNDEFINED;
      bool got_row = false;

      if (festate->is_generator) {
        JSValue next_fn = JS_GetPropertyStr(ctx, source, "next");
        if (JS_IsFunction(ctx, next_fn)) {
          JS_UpdateStackTop(JS_GetRuntime(ctx));
          JSValue step_val = JS_Call(ctx, next_fn, source, 0, NULL);
          JS_FreeValue(ctx, next_fn);
          if (JS_IsException(step_val)) {
            pljs_ereport_js_exception(ctx);
          }
          if (JS_IsObject(step_val)) {
            JSValue done_v = JS_GetPropertyStr(ctx, step_val, "done");
            bool is_done = JS_ToBool(ctx, done_v) != 0;
            JS_FreeValue(ctx, done_v);
            if (!is_done) {
              row_val = JS_GetPropertyStr(ctx, step_val, "value");
              got_row = (!JS_IsUndefined(row_val) && !JS_IsNull(row_val));
              if (!got_row) {
                JS_FreeValue(ctx, row_val);
                row_val = JS_UNDEFINED;
              }
            }
          }
          JS_FreeValue(ctx, step_val);
        } else {
          JS_FreeValue(ctx, next_fn);
        }
      } else if (festate->is_array) {
        if (festate->row_idx < festate->row_count) {
          row_val = JS_GetPropertyUint32(ctx, source, festate->row_idx++);
          if (JS_IsException(row_val)) {
            pljs_ereport_js_exception(ctx);
          }
          got_row = (!JS_IsUndefined(row_val) && !JS_IsNull(row_val));
          if (!got_row) {
            JS_FreeValue(ctx, row_val);
            row_val = JS_UNDEFINED;
          }
        }
      } else if (festate->is_func) {
        JS_UpdateStackTop(JS_GetRuntime(ctx));
        row_val = JS_Call(ctx, source, festate->wrapper_instance, 0, NULL);
        if (JS_IsException(row_val)) {
          pljs_ereport_js_exception(ctx);
        }
        got_row = (!JS_IsUndefined(row_val) && !JS_IsNull(row_val));
        if (!got_row) {
          JS_FreeValue(ctx, row_val);
          row_val = JS_UNDEFINED;
        }
      } else if (festate->row_idx == 0 && festate->row_count == 1) {
        festate->row_idx = 1;
        row_val = JS_DupValue(ctx, source);
        got_row = true;
      }

      if (!got_row) {
        festate->eof_reached = true;
        if (festate->active_cache_entry != NULL) {
          festate->active_cache_entry->complete = true;
        }
        ret_slot = ExecClearTuple(slot);
      } else {
        pljs_fdw_row_to_slot(ctx, row_val, slot, festate);
        JS_FreeValue(ctx, row_val);
        festate->emitted_rows++;

        if (festate->cache_results && festate->tuplestore != NULL) {
          MemoryContext ts_old = MemoryContextSwitchTo(festate->scan_mcxt);
          tuplestore_puttupleslot(festate->tuplestore, slot);
          if (festate->active_cache_entry != NULL) {
            festate->active_cache_entry->bytes += 256;
            festate->cache_current_bytes += 256;
          }
          MemoryContextSwitchTo(ts_old);
        }
        ret_slot = slot;
      }
    }
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
    MemoryContextSwitchTo(oldcxt);
  }
  PG_END_TRY();

  return ret_slot;
}

static void pljs_fdw_rescan_foreign_scan(ForeignScanState *node) {
  PljsFdwScanState *festate = (PljsFdwScanState *)node->fdw_state;
  if (!festate)
    return;

  ExprContext *econtext = node->ss.ps.ps_ExprContext;
  bool has_params = pljs_fdw_has_param_quals(festate);

  if (!festate->cache_results) {
    if (festate->tuplestore) {
      tuplestore_end(festate->tuplestore);
      festate->tuplestore = NULL;
    }
    festate->active_cache_entry = NULL;
    festate->reading_from_tuplestore = false;
    festate->scan_started = false;
    festate->eof_reached = false;
    return;
  }

  if (!has_params) {
    if (festate->scan_started && festate->eof_reached &&
        festate->tuplestore != NULL) {
      tuplestore_rescan(festate->tuplestore);
      festate->reading_from_tuplestore = true;
      festate->emitted_rows = 0;
      festate->stats_cache_hits++;
      return;
    }
    if (festate->tuplestore) {
      tuplestore_end(festate->tuplestore);
      festate->tuplestore = NULL;
    }
    festate->reading_from_tuplestore = false;
    festate->scan_started = false;
    festate->eof_reached = false;
    return;
  }

  char *param_key = pljs_fdw_build_param_cache_key(festate, econtext);
  PljsCacheEntry *found = pljs_fdw_lru_find(festate, param_key);
  if (found != NULL && found->complete && found->store != NULL) {
    pljs_fdw_lru_move_to_front(festate, found);
    festate->active_cache_entry = found;
    festate->tuplestore = found->store;
    tuplestore_rescan(festate->tuplestore);
    festate->reading_from_tuplestore = true;
    festate->eof_reached = false;
    festate->emitted_rows = 0;
    festate->stats_cache_hits++;
    pfree(param_key);
    return;
  }

  MemoryContext oldcxt = MemoryContextSwitchTo(festate->scan_mcxt);
  Tuplestorestate *new_store = tuplestore_begin_heap(true, false, work_mem);
  MemoryContextSwitchTo(oldcxt);

  if (found != NULL) {
    if (found->store != NULL) {
      tuplestore_end(found->store);
    }
    found->store = new_store;
    found->complete = false;
    pljs_fdw_lru_move_to_front(festate, found);
    festate->active_cache_entry = found;
  } else {
    festate->active_cache_entry = NULL;
    festate->active_cache_entry =
        pljs_fdw_lru_insert(festate, param_key, new_store);
  }

  festate->tuplestore = new_store;
  festate->reading_from_tuplestore = false;
  festate->scan_started = false;
  festate->eof_reached = false;
  festate->emitted_rows = 0;

  pfree(param_key);
}

static void pljs_fdw_end_foreign_scan(ForeignScanState *node) {
  PljsFdwScanState *festate = (PljsFdwScanState *)node->fdw_state;
  if (!festate)
    return;

  JSContext *ctx = festate->ctx;
  if (ctx != NULL) {
    if (!JS_IsUndefined(festate->iter_or_array)) {
      JS_FreeValue(ctx, festate->iter_or_array);
      festate->iter_or_array = JS_UNDEFINED;
    }
    if (!JS_IsUndefined(festate->wrapper_instance)) {
      JS_FreeValue(ctx, festate->wrapper_instance);
      festate->wrapper_instance = JS_UNDEFINED;
    }
  }

  Tuplestorestate *active_ts = festate->tuplestore;
  for (PljsCacheEntry *curr = festate->lru_head; curr != NULL;
       curr = curr->next) {
    if (curr->store) {
      if (curr->store == active_ts)
        active_ts = NULL;
      tuplestore_end(curr->store);
      curr->store = NULL;
    }
  }
  if (active_ts) {
    tuplestore_end(active_ts);
    festate->tuplestore = NULL;
  }

  MemoryContext scan_mcxt = festate->scan_mcxt;
  node->fdw_state = NULL;
  if (scan_mcxt) {
    MemoryContextDelete(scan_mcxt);
  }
}

/*
 * ---------- FDW Modify Callbacks ----------
 */

static void pljs_fdw_add_foreign_update_targets(PlannerInfo *root,
                                                Index rtindex,
                                                RangeTblEntry *target_rte,
                                                Relation target_relation) {
  Oid foreigntableid = RelationGetRelid(target_relation);
  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);

  const char *rowid_col = pljs_fdw_opt_get(&opts, "rowid_column");
  if (!rowid_col || rowid_col[0] == '\0') {
    rowid_col = pljs_fdw_opt_get(&opts, "key");
  }
  if (!rowid_col || rowid_col[0] == '\0') {
    rowid_col = pljs_fdw_opt_get(&opts, "pk");
  }

  TupleDesc tupdesc = RelationGetDescr(target_relation);
  Form_pg_attribute target_attr = NULL;

  if (rowid_col && rowid_col[0] != '\0') {
    for (int i = 0; i < tupdesc->natts; i++) {
      Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
      if (!attr->attisdropped &&
          strcmp(NameStr(attr->attname), rowid_col) == 0) {
        target_attr = attr;
        break;
      }
    }
  }
  if (!target_attr) {
    for (int i = 0; i < tupdesc->natts; i++) {
      Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
      if (!attr->attisdropped &&
          (strcmp(NameStr(attr->attname), "id") == 0 ||
           strcmp(NameStr(attr->attname), "key") == 0)) {
        target_attr = attr;
        break;
      }
    }
  }
  if (!target_attr && tupdesc->natts > 0) {
    for (int i = 0; i < tupdesc->natts; i++) {
      Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
      if (!attr->attisdropped) {
        target_attr = attr;
        break;
      }
    }
  }

  if (target_attr) {
    Var *var = makeVar(rtindex, target_attr->attnum, target_attr->atttypid,
                       target_attr->atttypmod, target_attr->attcollation, 0);
    add_row_identity_var(root, var, rtindex, "__pljs_rowid");
  }
  (void)target_rte;
}

static List *pljs_fdw_plan_foreign_modify(PlannerInfo *root, ModifyTable *plan,
                                          Index resultRelation,
                                          int subplan_index) {
  (void)root;
  (void)plan;
  (void)resultRelation;
  (void)subplan_index;
  return NIL;
}

static void pljs_fdw_begin_foreign_modify(ModifyTableState *mtstate,
                                          ResultRelInfo *rinfo,
                                          List *fdw_private, int subplan_index,
                                          int eflags) {
  (void)fdw_private;
  if (eflags & EXEC_FLAG_EXPLAIN_ONLY) {
    rinfo->ri_FdwState = NULL;
    return;
  }

  Relation rel = rinfo->ri_RelationDesc;
  Oid foreigntableid = RelationGetRelid(rel);
  EState *estate = mtstate->ps.state;

  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);

  MemoryContext modify_mcxt = AllocSetContextCreate(
      estate->es_query_cxt, "pljs_fdw modify state", ALLOCSET_DEFAULT_SIZES);
  MemoryContext oldcxt = MemoryContextSwitchTo(modify_mcxt);

  PljsFdwModifyState *fmstate =
      (PljsFdwModifyState *)palloc0(sizeof(PljsFdwModifyState));
  fmstate->user_id = GetUserId();
  fmstate->modify_mcxt = modify_mcxt;
  fmstate->foreigntableid = foreigntableid;
  fmstate->operation = mtstate->operation;
  fmstate->rowid_column = pstrdup("id");
  fmstate->rowid_attno = InvalidAttrNumber;
  fmstate->rowid_type = INT4OID;
  fmstate->batch_size = 1;
  fmstate->wrapper_instance = JS_UNDEFINED;

  fmstate->cleanup_cb.func = pljs_fdw_modify_cleanup_cb;
  fmstate->cleanup_cb.arg = fmstate;
  MemoryContextRegisterResetCallback(modify_mcxt, &fmstate->cleanup_cb);

  fmstate->type_io_flinfo.fn_oid = InvalidOid;
  fmstate->type_io_flinfo.fn_mcxt = modify_mcxt;

  const char *opt_bs = pljs_fdw_opt_get(&opts, "batch_size");
  if (opt_bs) {
    int bs = atoi(opt_bs);
    if (bs > 1)
      fmstate->batch_size = bs;
  }
  const char *opt_rc = pljs_fdw_opt_get(&opts, "rowid_column");
  if (opt_rc && opt_rc[0] != '\0') {
    fmstate->rowid_column = pstrdup(opt_rc);
  } else {
    const char *opt_pk = pljs_fdw_opt_get(&opts, "pk");
    if (opt_pk && opt_pk[0] != '\0') {
      fmstate->rowid_column = pstrdup(opt_pk);
    } else {
      const char *opt_key = pljs_fdw_opt_get(&opts, "key");
      if (opt_key && opt_key[0] != '\0') {
        fmstate->rowid_column = pstrdup(opt_key);
      }
    }
  }

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&fmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = pljs_fdw_get_context();
    fmstate->ctx = ctx;
    fmstate->wrapper_instance =
        pljs_fdw_get_wrapper_instance(ctx, foreigntableid, &opts);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  if (mtstate->operation == CMD_UPDATE || mtstate->operation == CMD_DELETE) {
    Plan *subplan = outerPlanState(mtstate)->plan;
    fmstate->rowid_attno =
        ExecFindJunkAttributeInTlist(subplan->targetlist, "__pljs_rowid");
    if (AttributeNumberIsValid(fmstate->rowid_attno)) {
      TargetEntry *tle =
          get_tle_by_resno(subplan->targetlist, fmstate->rowid_attno);
      if (tle && tle->expr) {
        fmstate->rowid_type = exprType((Node *)tle->expr);
      }
    }
  }

  MemoryContextSwitchTo(oldcxt);
  rinfo->ri_FdwState = (void *)fmstate;
  (void)subplan_index;
}

static JSValue pljs_fdw_slot_to_js(JSContext *ctx, TupleTableSlot *slot) {
  TupleDesc tupdesc = slot->tts_tupleDescriptor;
  slot_getallattrs(slot);
  JSValue obj = JS_NewObject(ctx);

  for (int i = 0; i < tupdesc->natts; i++) {
    Form_pg_attribute attr = TupleDescAttr(tupdesc, i);
    if (attr->attisdropped || attr->attnum <= 0)
      continue;

    bool isnull = slot->tts_isnull[i];
    JSValue val;
    if (isnull) {
      val = JS_NULL;
    } else {
      val = pljs_datum_to_jsvalue(attr->atttypid, slot->tts_values[i], false,
                                  true, ctx);
      if (JS_IsException(val)) {
        JS_FreeValue(ctx, obj);
        pljs_ereport_js_exception(ctx);
      }
    }
    JS_SetPropertyStr(ctx, obj, NameStr(attr->attname), val);
  }
  return obj;
}

static TupleTableSlot *pljs_fdw_exec_foreign_insert(EState *estate,
                                                    ResultRelInfo *rinfo,
                                                    TupleTableSlot *slot,
                                                    TupleTableSlot *planSlot) {
  (void)estate;
  (void)planSlot;
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)rinfo->ri_FdwState;
  if (!fmstate)
    return slot;

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&fmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = fmstate->ctx;
    JSValue row_obj = pljs_fdw_slot_to_js(ctx, slot);
    JSValue wrapper = fmstate->wrapper_instance;
    JSValue ins_val = JS_GetPropertyStr(ctx, wrapper, "insert");
    if (JS_IsFunction(ctx, ins_val)) {
      JSValue args[1] = {row_obj};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue ret_val = JS_Call(ctx, ins_val, wrapper, 1, args);
      JS_FreeValue(ctx, ins_val);
      JS_FreeValue(ctx, row_obj);
      if (JS_IsException(ret_val)) {
        pljs_ereport_js_exception(ctx);
      }
      if (JS_IsObject(ret_val) && !JS_IsNull(ret_val)) {
        pljs_fdw_row_to_slot(ctx, ret_val, slot, NULL);
      }
      JS_FreeValue(ctx, ret_val);
    } else {
      JS_FreeValue(ctx, ins_val);
      JS_FreeValue(ctx, row_obj);
    }
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  return slot;
}

static TupleTableSlot **
pljs_fdw_exec_foreign_batch_insert(EState *estate, ResultRelInfo *rinfo,
                                   TupleTableSlot **slots,
                                   TupleTableSlot **planSlots, int *numSlots) {
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)rinfo->ri_FdwState;
  if (!fmstate || *numSlots <= 0)
    return slots;

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&fmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = fmstate->ctx;
    JSValue wrapper = fmstate->wrapper_instance;
    JSValue batch_val = JS_GetPropertyStr(ctx, wrapper, "batchInsert");
    if (JS_IsFunction(ctx, batch_val)) {
      JSValue rows_arr = JS_NewArray(ctx);
      for (int i = 0; i < *numSlots; i++) {
        JS_SetPropertyUint32(ctx, rows_arr, (uint32_t)i,
                             pljs_fdw_slot_to_js(ctx, slots[i]));
      }
      JSValue args[1] = {rows_arr};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue ret_val = JS_Call(ctx, batch_val, wrapper, 1, args);
      JS_FreeValue(ctx, batch_val);
      JS_FreeValue(ctx, rows_arr);
      if (JS_IsException(ret_val)) {
        pljs_ereport_js_exception(ctx);
      }
      if (JS_IsArray(ctx, ret_val)) {
        int32_t rlen = pljs_js_array_length(ret_val, ctx);
        int limit = rlen < *numSlots ? (int)rlen : *numSlots;
        for (int i = 0; i < limit; i++) {
          JSValue r = JS_GetPropertyUint32(ctx, ret_val, (uint32_t)i);
          if (JS_IsObject(r) && !JS_IsNull(r)) {
            pljs_fdw_row_to_slot(ctx, r, slots[i], NULL);
          }
          JS_FreeValue(ctx, r);
        }
      }
      JS_FreeValue(ctx, ret_val);
    } else {
      JS_FreeValue(ctx, batch_val);
      for (int i = 0; i < *numSlots; i++) {
        pljs_fdw_exec_foreign_insert(
            estate, rinfo, slots[i], planSlots ? planSlots[i] : NULL);
      }
    }
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  return slots;
}

static int pljs_fdw_get_foreign_modify_batch_size(ResultRelInfo *rinfo) {
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)rinfo->ri_FdwState;
  return fmstate ? fmstate->batch_size : 1;
}

static TupleTableSlot *pljs_fdw_exec_foreign_update(EState *estate,
                                                    ResultRelInfo *rinfo,
                                                    TupleTableSlot *slot,
                                                    TupleTableSlot *planSlot) {
  (void)estate;
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)rinfo->ri_FdwState;
  if (!fmstate)
    return slot;

  if (!AttributeNumberIsValid(fmstate->rowid_attno)) {
    ereport(ERROR, (errcode(ERRCODE_FDW_ERROR),
                    errmsg("pljs_fdw: missing rowid junk attribute for UPDATE")));
  }

  bool isnull = false;
  Datum rowid_datum =
      ExecGetJunkAttribute(planSlot, fmstate->rowid_attno, &isnull);
  if (isnull) {
    ereport(ERROR, (errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
                    errmsg("pljs_fdw: rowid junk attribute is null")));
  }

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&fmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = fmstate->ctx;
    JSValue rowid_val =
        pljs_datum_to_jsvalue(fmstate->rowid_type, rowid_datum, false, true, ctx);
    if (JS_IsException(rowid_val)) {
      pljs_ereport_js_exception(ctx);
    }
    JSValue row_obj = pljs_fdw_slot_to_js(ctx, slot);
    JSValue wrapper = fmstate->wrapper_instance;
    JSValue upd_val = JS_GetPropertyStr(ctx, wrapper, "update");
    if (JS_IsFunction(ctx, upd_val)) {
      JSValue args[2] = {rowid_val, row_obj};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue ret_val = JS_Call(ctx, upd_val, wrapper, 2, args);
      JS_FreeValue(ctx, upd_val);
      JS_FreeValue(ctx, rowid_val);
      JS_FreeValue(ctx, row_obj);
      if (JS_IsException(ret_val)) {
        pljs_ereport_js_exception(ctx);
      }
      if (JS_IsObject(ret_val) && !JS_IsNull(ret_val)) {
        pljs_fdw_row_to_slot(ctx, ret_val, slot, NULL);
      }
      JS_FreeValue(ctx, ret_val);
    } else {
      JS_FreeValue(ctx, upd_val);
      JS_FreeValue(ctx, rowid_val);
      JS_FreeValue(ctx, row_obj);
    }
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  return slot;
}

static TupleTableSlot *pljs_fdw_exec_foreign_delete(EState *estate,
                                                    ResultRelInfo *rinfo,
                                                    TupleTableSlot *slot,
                                                    TupleTableSlot *planSlot) {
  (void)estate;
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)rinfo->ri_FdwState;
  if (!fmstate)
    return slot;

  if (!AttributeNumberIsValid(fmstate->rowid_attno)) {
    ereport(ERROR, (errcode(ERRCODE_FDW_ERROR),
                    errmsg("pljs_fdw: missing rowid junk attribute for DELETE")));
  }

  bool isnull = false;
  Datum rowid_datum =
      ExecGetJunkAttribute(planSlot, fmstate->rowid_attno, &isnull);
  if (isnull) {
    ereport(ERROR, (errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
                    errmsg("pljs_fdw: rowid junk attribute is null")));
  }

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&fmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = fmstate->ctx;
    JSValue rowid_val =
        pljs_datum_to_jsvalue(fmstate->rowid_type, rowid_datum, false, true, ctx);
    if (JS_IsException(rowid_val)) {
      pljs_ereport_js_exception(ctx);
    }
    JSValue wrapper = fmstate->wrapper_instance;
    JSValue del_val = JS_GetPropertyStr(ctx, wrapper, "delete");
    if (JS_IsFunction(ctx, del_val)) {
      JSValue args[1] = {rowid_val};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue ret_val = JS_Call(ctx, del_val, wrapper, 1, args);
      JS_FreeValue(ctx, del_val);
      JS_FreeValue(ctx, rowid_val);
      if (JS_IsException(ret_val)) {
        pljs_ereport_js_exception(ctx);
      }
      JS_FreeValue(ctx, ret_val);
    } else {
      JS_FreeValue(ctx, del_val);
      JS_FreeValue(ctx, rowid_val);
    }
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  return slot;
}

static void pljs_fdw_end_foreign_modify(EState *estate, ResultRelInfo *rinfo) {
  (void)estate;
  PljsFdwModifyState *fmstate = (PljsFdwModifyState *)rinfo->ri_FdwState;
  if (!fmstate)
    return;

  if (fmstate->ctx != NULL && !JS_IsUndefined(fmstate->wrapper_instance)) {
    JS_FreeValue(fmstate->ctx, fmstate->wrapper_instance);
    fmstate->wrapper_instance = JS_UNDEFINED;
  }

  MemoryContext modify_mcxt = fmstate->modify_mcxt;
  rinfo->ri_FdwState = NULL;
  if (modify_mcxt) {
    MemoryContextDelete(modify_mcxt);
  }
}

static int pljs_fdw_is_foreign_rel_updatable(Relation rel) {
  (void)rel;
  return (1 << CMD_INSERT) | (1 << CMD_UPDATE) | (1 << CMD_DELETE);
}

/*
 * ---------- FDW Direct Modify Callbacks ----------
 */

static ForeignScan *pljs_fdw_find_modifytable_subplan(PlannerInfo *root,
                                                      ModifyTable *plan,
                                                      Index resultRelation,
                                                      int subplan_index) {
  (void)root;
  (void)resultRelation;
  (void)subplan_index;
  Plan *subplan = outerPlan(plan);
  if (subplan && IsA(subplan, ForeignScan)) {
    return (ForeignScan *)subplan;
  }
  return NULL;
}

static bool pljs_fdw_plan_direct_modify(PlannerInfo *root, ModifyTable *plan,
                                        Index resultRelation,
                                        int subplan_index) {
  CmdType operation = plan->operation;
  if (operation != CMD_DELETE)
    return false;

  ForeignScan *fscan = pljs_fdw_find_modifytable_subplan(
      root, plan, resultRelation, subplan_index);
  if (!fscan)
    return false;

  if (fscan->scan.plan.qual != NIL)
    return false;

  Oid foreigntableid = root->simple_rte_array[resultRelation]->relid;
  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);
  const char *dm_opt = pljs_fdw_opt_get(&opts, "direct_modify");
  if (!dm_opt || (strcmp(dm_opt, "true") != 0 && strcmp(dm_opt, "on") != 0))
    return false;

  fscan->operation = operation;
  fscan->resultRelation = resultRelation;
  fscan->fdw_private = lappend(fscan->fdw_private, makeInteger((int)operation));
  return true;
}

static void pljs_fdw_begin_direct_modify(ForeignScanState *node, int eflags) {
  if (eflags & EXEC_FLAG_EXPLAIN_ONLY) {
    node->fdw_state = NULL;
    return;
  }

  ForeignScan *plan = (ForeignScan *)node->ss.ps.plan;
  Oid foreigntableid = RelationGetRelid(node->ss.ss_currentRelation);
  CmdType operation = CMD_UNKNOWN;
  if (plan->fdw_private != NIL) {
    Node *last_n = (Node *)llast(plan->fdw_private);
    if (last_n && IsA(last_n, Integer)) {
      operation = (CmdType)intVal(last_n);
    }
  }

  PljsFdwOptions opts;
  pljs_fdw_get_options(foreigntableid, &opts);

  MemoryContext direct_mcxt = AllocSetContextCreate(
      node->ss.ps.state->es_query_cxt, "pljs_fdw direct modify context",
      ALLOCSET_DEFAULT_SIZES);
  MemoryContext oldcxt = MemoryContextSwitchTo(direct_mcxt);

  PljsFdwDirectModifyState *dmstate = (PljsFdwDirectModifyState *)palloc0(
      sizeof(PljsFdwDirectModifyState));
  dmstate->user_id = GetUserId();
  dmstate->direct_mcxt = direct_mcxt;
  dmstate->operation = operation;
  dmstate->has_executed = false;
  dmstate->affected_rows = 0;
  dmstate->set_processed =
      (node->resultRelInfo == NULL ||
       node->resultRelInfo->ri_projectReturning == NULL);
  dmstate->wrapper_instance = JS_UNDEFINED;

  dmstate->cleanup_cb.func = pljs_fdw_direct_modify_cleanup_cb;
  dmstate->cleanup_cb.arg = dmstate;
  MemoryContextRegisterResetCallback(direct_mcxt, &dmstate->cleanup_cb);

  dmstate->type_io_flinfo.fn_oid = InvalidOid;
  dmstate->type_io_flinfo.fn_mcxt = direct_mcxt;

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&dmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = pljs_fdw_get_context();
    dmstate->ctx = ctx;
    dmstate->wrapper_instance =
        pljs_fdw_get_wrapper_instance(ctx, foreigntableid, &opts);
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  TupleDesc tupdesc = RelationGetDescr(node->ss.ss_currentRelation);
  int n_exprs = list_length(plan->fdw_exprs);
  if (n_exprs > 0) {
    dmstate->quals = (PljsQual *)palloc0(sizeof(PljsQual) * (size_t)n_exprs);
  }
  ListCell *lc;
  foreach (lc, plan->fdw_exprs) {
    Node *clause = (Node *)lfirst(lc);
    PljsQual q;
    if (pljs_fdw_extract_qual(clause, plan->scan.scanrelid, tupdesc, &q)) {
      if (q.is_param && q.right_expr) {
        q.expr_state = ExecInitExpr((Expr *)q.right_expr, (PlanState *)node);
      }
      dmstate->quals[dmstate->quals_count++] = q;
    }
  }

  MemoryContextSwitchTo(oldcxt);
  node->fdw_state = (void *)dmstate;
}

static TupleTableSlot *pljs_fdw_iterate_direct_modify(ForeignScanState *node) {
  PljsFdwDirectModifyState *dmstate =
      (PljsFdwDirectModifyState *)node->fdw_state;
  TupleTableSlot *slot = node->ss.ss_ScanTupleSlot;
  if (!dmstate || dmstate->has_executed) {
    return ExecClearTuple(slot);
  }

  dmstate->has_executed = true;

  pljs_encoding_init();
  pljs_type_io_cache *saved_types =
      pljs_type_io_enter(&dmstate->type_io_flinfo);

  PG_TRY();
  {
    JSContext *ctx = dmstate->ctx;
    JSValue wrapper = dmstate->wrapper_instance;
    JSValue dm_fn = JS_GetPropertyStr(ctx, wrapper, "directModify");
    if (JS_IsFunction(ctx, dm_fn)) {
      const char *op_str =
          (dmstate->operation == CMD_UPDATE) ? "UPDATE" : "DELETE";
      JSValue op_js = JS_NewString(ctx, op_str);
      ExprContext *econtext = node->ss.ps.ps_ExprContext;
      JSValue quals_arr = JS_NewArray(ctx);
      for (int i = 0; i < dmstate->quals_count; i++) {
        JS_SetPropertyUint32(ctx, quals_arr, (uint32_t)i,
                             pljs_fdw_qual_to_js(ctx, &dmstate->quals[i],
                                                 econtext));
      }
      JSValue updates_obj = JS_NewObject(ctx);
      JSValue args[3] = {op_js, quals_arr, updates_obj};
      JS_UpdateStackTop(JS_GetRuntime(ctx));
      JSValue ret_val = JS_Call(ctx, dm_fn, wrapper, 3, args);
      JS_FreeValue(ctx, dm_fn);
      JS_FreeValue(ctx, op_js);
      JS_FreeValue(ctx, quals_arr);
      JS_FreeValue(ctx, updates_obj);
      if (JS_IsException(ret_val)) {
        pljs_ereport_js_exception(ctx);
      }
      if (JS_IsNumber(ret_val)) {
        int64_t n = 0;
        JS_ToInt64(ctx, &n, ret_val);
        dmstate->affected_rows = (int64)n;
      }
      JS_FreeValue(ctx, ret_val);
    } else {
      JS_FreeValue(ctx, dm_fn);
    }

    if (dmstate->set_processed) {
      node->ss.ps.state->es_processed += dmstate->affected_rows;
    }
  }
  PG_FINALLY();
  {
    pljs_type_io_exit(saved_types);
  }
  PG_END_TRY();

  return ExecClearTuple(slot);
}

static void pljs_fdw_end_direct_modify(ForeignScanState *node) {
  PljsFdwDirectModifyState *dmstate =
      (PljsFdwDirectModifyState *)node->fdw_state;
  if (!dmstate)
    return;

  if (dmstate->ctx != NULL && !JS_IsUndefined(dmstate->wrapper_instance)) {
    JS_FreeValue(dmstate->ctx, dmstate->wrapper_instance);
    dmstate->wrapper_instance = JS_UNDEFINED;
  }

  MemoryContext direct_mcxt = dmstate->direct_mcxt;
  node->fdw_state = NULL;
  if (direct_mcxt) {
    MemoryContextDelete(direct_mcxt);
  }
}

/*
 * ---------- FDW Explain, Analyze & Schema Callbacks ----------
 */

static void pljs_fdw_explain_foreign_scan(ForeignScanState *node,
                                          ExplainState *es) {
  ForeignScan *plan = (ForeignScan *)node->ss.ps.plan;
  if (plan && plan->fdw_private != NIL &&
      list_length(plan->fdw_private) >= 1) {
    Node *n = (Node *)linitial(plan->fdw_private);
    if (n && IsA(n, Integer)) {
      int64 lim = (int64)intVal(n);
      if (lim >= 0) {
        ExplainPropertyInteger("Pushed Limit", NULL, lim, es);
      }
    }
  }

  PljsFdwScanState *festate = (PljsFdwScanState *)node->fdw_state;
  if (!festate)
    return;

  if (festate->stats_cache_hits > 0 || festate->stats_cache_misses > 0) {
    ExplainPropertyInteger("Cache Hits", "hits", festate->stats_cache_hits, es);
    ExplainPropertyInteger("Cache Misses", "misses",
                           festate->stats_cache_misses, es);
  }
}

static int pljs_fdw_acquire_sample_rows(Relation relation, int elevel,
                                        HeapTuple *rows, int targrows,
                                        double *totalrows,
                                        double *totaldeadrows) {
  (void)relation;
  (void)elevel;
  (void)rows;
  (void)targrows;
  *totalrows = 100.0;
  *totaldeadrows = 0.0;
  return 0;
}

static bool pljs_fdw_analyze_foreign_table(Relation relation,
                                           AcquireSampleRowsFunc *func,
                                           BlockNumber *totalpages) {
  (void)relation;
  *totalpages = 10;
  *func = pljs_fdw_acquire_sample_rows;
  return true;
}

static List *pljs_fdw_import_foreign_schema(ImportForeignSchemaStmt *stmt,
                                            Oid serverOid) {
  (void)stmt;
  (void)serverOid;
  return NIL;
}

/*
 * ---------- Validator & Handler Entry Points ----------
 */

Datum pljs_fdw_validator(PG_FUNCTION_ARGS) {
  ArrayType *array = PG_GETARG_ARRAYTYPE_P(0);
  Oid catalog = PG_GETARG_OID(1);
  (void)catalog;

  static const char *valid_opts[] = {
      "wrapper",       "cache_results", "cache_size", "cache_memory_limit",
      "rowid_column",  "batch_size",    "key",        "pk",
      "seed",          "limit",         "direct_modify",
      NULL};

  List *options = untransformRelOptions((Datum)PointerGetDatum(array));
  ListCell *lc;

  foreach (lc, options) {
    DefElem *def = (DefElem *)lfirst(lc);
    bool found = false;
    for (int i = 0; valid_opts[i] != NULL; i++) {
      if (strcmp(def->defname, valid_opts[i]) == 0) {
        found = true;
        break;
      }
    }
    if (!found) {
      ereport(ERROR, (errcode(ERRCODE_FDW_INVALID_OPTION_NAME),
                      errmsg("pljs_fdw: invalid option \"%s\"", def->defname)));
    }
  }

  PG_RETURN_VOID();
}

Datum pljs_fdw_handler(PG_FUNCTION_ARGS) {
  FdwRoutine *routine = makeNode(FdwRoutine);

  routine->GetForeignRelSize = pljs_fdw_get_foreign_rel_size;
  routine->GetForeignPaths = pljs_fdw_get_foreign_paths;
  routine->GetForeignPlan = pljs_fdw_get_foreign_plan;
  routine->BeginForeignScan = pljs_fdw_begin_foreign_scan;
  routine->IterateForeignScan = pljs_fdw_iterate_foreign_scan;
  routine->ReScanForeignScan = pljs_fdw_rescan_foreign_scan;
  routine->EndForeignScan = pljs_fdw_end_foreign_scan;

  routine->AddForeignUpdateTargets = pljs_fdw_add_foreign_update_targets;
  routine->PlanForeignModify = pljs_fdw_plan_foreign_modify;
  routine->BeginForeignModify = pljs_fdw_begin_foreign_modify;
  routine->ExecForeignInsert = pljs_fdw_exec_foreign_insert;
  routine->ExecForeignBatchInsert = pljs_fdw_exec_foreign_batch_insert;
  routine->GetForeignModifyBatchSize = pljs_fdw_get_foreign_modify_batch_size;
  routine->ExecForeignUpdate = pljs_fdw_exec_foreign_update;
  routine->ExecForeignDelete = pljs_fdw_exec_foreign_delete;
  routine->EndForeignModify = pljs_fdw_end_foreign_modify;
  routine->IsForeignRelUpdatable = pljs_fdw_is_foreign_rel_updatable;

  routine->PlanDirectModify = pljs_fdw_plan_direct_modify;
  routine->BeginDirectModify = pljs_fdw_begin_direct_modify;
  routine->IterateDirectModify = pljs_fdw_iterate_direct_modify;
  routine->EndDirectModify = pljs_fdw_end_direct_modify;

  routine->ExplainForeignScan = pljs_fdw_explain_foreign_scan;
  routine->AnalyzeForeignTable = pljs_fdw_analyze_foreign_table;
  routine->ImportForeignSchema = pljs_fdw_import_foreign_schema;

  PG_RETURN_POINTER(routine);
}
