CREATE FUNCTION crash_test() RETURNS boolean
LANGUAGE pljs IMMUTABLE STRICT
AS $$
  var a = new ArrayBuffer(8);
  return true;
$$;

SELECT crash_test();

-- ES6 / harmony features
CREATE TABLE rectangle (
  id    INTEGER,
  data  JSON
);

INSERT INTO rectangle (id, data) VALUES
(1, '{"width": 20.3, "height": 1.5}'),
(2, '{"width": 10.2, "height": 9.5}'),
(3, '{"width": 3.5,  "height": 5.2}'),
(4, '{"width": 8.2,  "height": 8.2}'),
(5, '{"width": 9.4,  "height": 0.2}'),
(6, '{"width": 1.2,  "height": 1.5}');

-- for..of loop over result array with break
CREATE OR REPLACE FUNCTION get_rectangles_area(min_area NUMERIC)
RETURNS json AS $$
  var rectangles = pljs.execute('SELECT id, data FROM rectangle ORDER BY id');
  var result = [];
  var area = 0.0;
  for (var rectangle of rectangles) {
    area += rectangle.data.width * rectangle.data.height;
    result.push({id: rectangle.id, data: rectangle.data});
    if (area >= min_area) {
      break;
    }
  }
  return result;
$$ LANGUAGE pljs STABLE STRICT;

SELECT get_rectangles_area(130.0);

-- same for..of loop, this time using a cursor within a generator
CREATE OR REPLACE FUNCTION get_rectangles_area(min_area NUMERIC)
RETURNS json AS $$
  var plan = pljs.prepare('SELECT id, data FROM rectangle ORDER BY id');
  var cursor = plan.cursor();
  var generator = function* () {
    var row;
    while (row = cursor.fetch()) {
      yield row;
    }
  };
  var rectangles = generator();
  var result = [];
  var area = 0.0;
  for (var rectangle of rectangles) {
    area += rectangle.data.width * rectangle.data.height;
    result.push({id: rectangle.id, data: rectangle.data});
    if (area >= min_area) {
      break;
    }
  }
  cursor.close();
  plan.free();
  return result;
$$ LANGUAGE pljs STABLE STRICT;

SELECT get_rectangles_area(130.0);

-- Issue: Preserve original SQLSTATE and diagnostics across subtransactions
CREATE TABLE subxact_err_tbl (
    id int PRIMARY KEY,
    val int NOT NULL CHECK (val > 0)
);
INSERT INTO subxact_err_tbl VALUES (1, 10);

CREATE OR REPLACE FUNCTION test_subxact_unique_violation() RETURNS void AS $$
    pljs.subtransaction(function() {
        pljs.execute("INSERT INTO subxact_err_tbl VALUES (1, 20)");
    });
$$ LANGUAGE pljs;

DO $$
DECLARE
    v_state text;
    v_msg text;
    v_detail text;
    v_constraint text;
    v_table text;
BEGIN
    PERFORM test_subxact_unique_violation();
EXCEPTION WHEN unique_violation THEN
    GET STACKED DIAGNOSTICS
        v_state = RETURNED_SQLSTATE,
        v_msg = MESSAGE_TEXT,
        v_detail = PG_EXCEPTION_DETAIL,
        v_constraint = CONSTRAINT_NAME,
        v_table = TABLE_NAME;
    RAISE NOTICE 'caught unique_violation: state=%, table=%, constraint=%, detail=%',
        v_state, v_table, v_constraint, v_detail;
END;
$$;

CREATE OR REPLACE FUNCTION test_custom_js_sqlstate() RETURNS void AS $$
    var err = new Error("custom check violation from JS");
    err.sqlerrcode = "23514";
    err.detail = "val must be positive";
    err.hint = "pass a value > 0";
    err.table_name = "subxact_err_tbl";
    err.constraint_name = "subxact_err_tbl_val_check";
    throw err;
$$ LANGUAGE pljs;

DO $$
DECLARE
    v_state text;
    v_msg text;
    v_detail text;
    v_hint text;
    v_constraint text;
BEGIN
    PERFORM test_custom_js_sqlstate();
EXCEPTION WHEN check_violation THEN
    GET STACKED DIAGNOSTICS
        v_state = RETURNED_SQLSTATE,
        v_msg = MESSAGE_TEXT,
        v_detail = PG_EXCEPTION_DETAIL,
        v_hint = PG_EXCEPTION_HINT,
        v_constraint = CONSTRAINT_NAME;
    RAISE NOTICE 'caught check_violation: state=%, msg=%, detail=%, hint=%, constraint=%',
        v_state, v_msg, v_detail, v_hint, v_constraint;
END;
$$;

DROP FUNCTION test_subxact_unique_violation();
DROP FUNCTION test_custom_js_sqlstate();
DROP TABLE subxact_err_tbl;
