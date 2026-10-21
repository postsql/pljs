CREATE OR REPLACE FUNCTION pljs_call_handler() RETURNS language_handler
AS 'MODULE_PATHNAME' LANGUAGE C;

CREATE OR REPLACE FUNCTION pljs_call_validator(oid) RETURNS void
	AS 'MODULE_PATHNAME' LANGUAGE C;

CREATE OR REPLACE FUNCTION pljs_inline_handler(internal) RETURNS void
  AS 'MODULE_PATHNAME' LANGUAGE C;

CREATE OR REPLACE TRUSTED LANGUAGE pljs
 HANDLER pljs_call_handler
 INLINE pljs_inline_handler
 VALIDATOR pljs_call_validator;

CREATE OR REPLACE FUNCTION pljs_version()
 RETURNS TEXT
 AS 'MODULE_PATHNAME', 'pljs_version'
 LANGUAGE C STRICT IMMUTABLE;

CREATE OR REPLACE FUNCTION pljs_info() RETURNS JSON
 AS 'MODULE_PATHNAME', 'pljs_info'
 LANGUAGE C;

CREATE OR REPLACE FUNCTION pljs_reset() RETURNS void
 AS 'MODULE_PATHNAME', 'pljs_reset'
 LANGUAGE C;

-- These act on the whole session rather than on one function: pljs_info shows
-- its memory and configuration, and pljs_reset discards the cached contexts of
-- every user in it.  They are for superusers, or the roles they are granted to.
REVOKE ALL ON FUNCTION pljs_info() FROM PUBLIC;
REVOKE ALL ON FUNCTION pljs_reset() FROM PUBLIC;

CREATE SCHEMA IF NOT EXISTS pljs;
GRANT USAGE ON SCHEMA pljs TO PUBLIC;

CREATE TABLE IF NOT EXISTS pljs.packages (
  name TEXT NOT NULL,
  version TEXT NOT NULL,
  entry_point TEXT NOT NULL,
  dependencies JSONB DEFAULT '{}',
  created_at TIMESTAMP WITH TIME ZONE NOT NULL DEFAULT NOW(),
  updated_at TIMESTAMP WITH TIME ZONE,
  PRIMARY KEY (name, version)
);

CREATE TABLE IF NOT EXISTS pljs.modules (
  path TEXT NOT NULL,
  source TEXT,
  package_name TEXT,
  package_version TEXT,
  created_at TIMESTAMP WITH TIME ZONE NOT NULL DEFAULT NOW(),
  updated_at TIMESTAMP WITH TIME ZONE,
  -- A CommonJS module that needs sloppy mode (implicit globals, `with`, octal
  -- literals) rather than the strict mode an ES module imposes.  Has no effect
  -- on an ES module, which is always strict.
  sloppy BOOLEAN NOT NULL DEFAULT false,
  bytecode BYTEA,
  requires TEXT[],
  is_trusted BOOLEAN NOT NULL DEFAULT true,
  FOREIGN KEY (package_name, package_version) REFERENCES pljs.packages (name, version)
);

GRANT SELECT ON pljs.packages TO PUBLIC;
GRANT SELECT ON pljs.modules TO PUBLIC;

-- What is installed in these tables is the user's, not the extension's, so a
-- dump has to include it: without this, pg_dump skips the tables' contents and
-- a restore leaves them empty.
SELECT pg_catalog.pg_extension_config_dump('pljs.packages', '');
SELECT pg_catalog.pg_extension_config_dump('pljs.modules', '');

CREATE UNIQUE INDEX IF NOT EXISTS pljs_modules_standalone_path ON pljs.modules (path)
  WHERE package_name IS NULL;
CREATE UNIQUE INDEX IF NOT EXISTS pljs_modules_package_path ON pljs.modules (package_name, package_version, path)
  WHERE package_name IS NOT NULL;

-- Non-partial indexes for catalog scans (systable_beginscan_ordered).
CREATE INDEX IF NOT EXISTS pljs_modules_path ON pljs.modules (path);
CREATE INDEX IF NOT EXISTS pljs_modules_pkg ON pljs.modules (package_name, package_version, path);
CREATE INDEX IF NOT EXISTS pljs_packages_name ON pljs.packages (name);

-- Changing the module tables invalidates every backend's loaded modules: this
-- trigger makes the change visible to them (see src/modules.c).  It is ENABLE
-- ALWAYS so that replication and restores keep invalidating too.
CREATE OR REPLACE FUNCTION pljs_modules_changed() RETURNS trigger
 AS 'MODULE_PATHNAME', 'pljs_modules_changed'
 LANGUAGE C;

CREATE TRIGGER pljs_modules_guard
  BEFORE INSERT OR UPDATE OR DELETE ON pljs.modules
  FOR EACH ROW EXECUTE FUNCTION pljs_modules_changed();
ALTER TABLE pljs.modules ENABLE ALWAYS TRIGGER pljs_modules_guard;

CREATE TRIGGER pljs_modules_changed
  AFTER INSERT OR UPDATE OR DELETE OR TRUNCATE ON pljs.modules
  FOR EACH STATEMENT EXECUTE FUNCTION pljs_modules_changed();
ALTER TABLE pljs.modules ENABLE ALWAYS TRIGGER pljs_modules_changed;

CREATE TRIGGER pljs_modules_changed
  AFTER INSERT OR UPDATE OR DELETE OR TRUNCATE ON pljs.packages
  FOR EACH STATEMENT EXECUTE FUNCTION pljs_modules_changed();
ALTER TABLE pljs.packages ENABLE ALWAYS TRIGGER pljs_modules_changed;

CREATE TYPE pljs_source;
CREATE OR REPLACE FUNCTION pljs_source_in(cstring) RETURNS pljs_source
 AS 'MODULE_PATHNAME', 'pljs_source_in' LANGUAGE C IMMUTABLE STRICT;
CREATE OR REPLACE FUNCTION pljs_source_out(pljs_source) RETURNS cstring
 AS 'MODULE_PATHNAME', 'pljs_source_out' LANGUAGE C IMMUTABLE STRICT;
CREATE TYPE pljs_source (
 INPUT = pljs_source_in,
 OUTPUT = pljs_source_out,
 INTERNALLENGTH = VARIABLE,
 STORAGE = EXTENDED,
 CATEGORY = 'S'
);
CREATE CAST (text AS pljs_source) WITH INOUT AS IMPLICIT;
CREATE CAST (pljs_source AS text) WITH INOUT AS IMPLICIT;
CREATE CAST (varchar AS pljs_source) WITH INOUT AS IMPLICIT;
CREATE CAST (pljs_source AS varchar) WITH INOUT AS IMPLICIT;

CREATE OR REPLACE FUNCTION pljs_call_support(internal) RETURNS internal
 AS 'MODULE_PATHNAME', 'pljs_call_support' LANGUAGE C;
REVOKE ALL ON FUNCTION pljs_call_support(internal) FROM PUBLIC;

DO $$ BEGIN
  CREATE TYPE pljs.pljs_single_col_holder AS (__col1 text);
EXCEPTION WHEN duplicate_object THEN NULL;
END $$;

CREATE OR REPLACE FUNCTION pljs_inline_helper_0() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_1() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_2() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_3() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_4() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_5() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_6() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;
CREATE OR REPLACE FUNCTION pljs_inline_helper_7() RETURNS SETOF record
 LANGUAGE sql STABLE AS $$ SELECT 1 WHERE false $$;

CREATE OR REPLACE FUNCTION pljs_fdw_handler() RETURNS fdw_handler
 AS 'MODULE_PATHNAME', 'pljs_fdw_handler' LANGUAGE C STRICT;

CREATE OR REPLACE FUNCTION pljs_fdw_validator(text[], oid) RETURNS void
 AS 'MODULE_PATHNAME', 'pljs_fdw_validator' LANGUAGE C STRICT;

DO $$ BEGIN
  IF NOT EXISTS (SELECT 1 FROM pg_foreign_data_wrapper WHERE fdwname = 'pljs_fdw') THEN
    CREATE FOREIGN DATA WRAPPER pljs_fdw
      HANDLER pljs_fdw_handler
      VALIDATOR pljs_fdw_validator;
  END IF;
END $$;
