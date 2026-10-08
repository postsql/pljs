-- Test cross-extension integration between pg_tle and pljs
CREATE EXTENSION IF NOT EXISTS pg_tle;
CREATE EXTENSION IF NOT EXISTS pljs;

-- 1. Install modules via pgtle.install_module() and pljs.compile_bytecode()
SELECT pgtle.install_module(
    'tle-math',
    '1.0.0',
    'export function hypot(a, b) { return Math.sqrt(a * a + b * b); }'
);

DO LANGUAGE pljs $$
  const src = 'import { hypot } from "tle:tle-math@1.0.0"; export function dist(x1, y1, x2, y2) { return hypot(x2 - x1, y2 - y1); }';
  const bc = pljs.compile_bytecode(src, 'tle-geom@1.0.0');
  pljs.execute(
    'SELECT pgtle.install_module($1, $2, $3, $4)',
    ['tle-geom', '1.0.0', src, bc]
  );
$$;

-- 2. Verify SPI cache mode resolution
SET pgtle.module_cache_mode = 'spi';

CREATE OR REPLACE FUNCTION pljs_tle_dist(x1 float8, y1 float8, x2 float8, y2 float8)
RETURNS float8 LANGUAGE pljs AS $$
  import { dist } from 'tle:tle-geom@1.0.0';
  return dist(x1, y1, x2, y2);
$$;

SELECT pljs_tle_dist(0, 0, 3, 4);

-- 3. Verify shared-memory (DSA + dshash) cache mode resolution via pg_tle C API
SET pgtle.module_cache_mode = 'shared';

SELECT pljs_tle_dist(1, 2, 4, 6);

-- 4. Verify module upgrade and cache invalidation across pg_tle and pljs
SELECT pgtle.install_module(
    'tle-geom',
    '1.0.0',
    'import { hypot } from "tle:tle-math@1.0.0"; export function dist(x1, y1, x2, y2) { return hypot(x2 - x1, y2 - y1) * 10; }'
);

SELECT pljs_tle_dist(0, 0, 3, 4);

DROP FUNCTION pljs_tle_dist(float8, float8, float8, float8);
SELECT pgtle.uninstall_module('tle-geom', '1.0.0');
SELECT pgtle.uninstall_module('tle-math', '1.0.0');
DROP EXTENSION pg_tle CASCADE;
