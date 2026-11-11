#!/usr/bin/env python3
"""The Python binding against the Lean reference: every row of the shared vectors (vbm-json-vectors-1: verdict, error code, canonical form; the JSONTestSuite y_/n_/i_ files are set `jts`).
Usage: test_python.py VECTORS.jsonl [PACKAGE_PARENT_DIR]. Needs VBM_JSON_LIB (scripts/build_shared.sh). A row's accepted input must parse and print (here, in the test) to the reference's canonical
bytes; a rejected one must raise the Error subclass whose .name is the reference's code. A DRIVER: it holds no input of its own (the deep, duplicate-key, lexeme and empty inputs are rows of the generated set).
The binding's number= option and the Error codes are checked on those rows."""
import json, sys
sys.setrecursionlimit(20000)
if len(sys.argv) > 2: sys.path.insert(0, sys.argv[2])
import vbm_json
from vbm_json import Number, Object

ESC = {0x22: b'\\"', 0x5C: b"\\\\", 8: b"\\b", 12: b"\\f", 10: b"\\n", 13: b"\\r", 9: b"\\t"}

def canon(v):
    if v is None: return b"null"
    if v is True: return b"true"
    if v is False: return b"false"
    if isinstance(v, Number): return v.lexeme.encode()
    if isinstance(v, str):
        o = bytearray(b'"')
        for b in v.encode("utf-8"):
            o += ESC.get(b) or (b"\\u00%02x" % b if b < 0x20 else bytes([b]))
        return bytes(o + b'"')
    if isinstance(v, Object): return b"{" + b",".join(canon(k) + b":" + canon(x) for k, x in v) + b"}"
    if isinstance(v, list): return b"[" + b",".join(canon(x) for x in v) + b"]"
    raise TypeError(type(v))

def main():
    rows = ok = errs = 0
    sets = {}; rows_sample = []; codes = {}
    for line in open(sys.argv[1]):
        r = json.loads(line)
        rows += 1; sets[r["set"]] = sets.get(r["set"], 0) + 1
        data = bytes.fromhex(r["input"])
        where = "%s #%s" % (r["set"], r["id"])
        try:
            v = vbm_json.parse(data)
        except vbm_json.Error as e:
            if r["verdict"] != "err": sys.exit("test_python: %s: expected ok, got %s" % (where, e))
            if e.name.lower() != r["code"]: sys.exit("test_python: %s: expected code %s, got %s" % (where, r["code"], e.name))
            errs += 1; codes.setdefault(r["code"], e)
            continue
        if r["verdict"] != "ok": sys.exit("test_python: %s: expected error %s, but it parsed" % (where, r.get("code")))
        if canon(v).hex() != r["canonical"]: sys.exit("test_python: %s: canonical form differs: %s vs %s" % (where, canon(v).hex(), r["canonical"]))
        ok += 1
        if vbm_json.compact(data).hex() != r["canonical"]: sys.exit("test_python: %s: compact() differs from the canonical form" % where)
        if len(rows_sample) < 2000: rows_sample.append(r)
        if isinstance(v, str) and vbm_json.escape_string(v) != bytes.fromhex(r["canonical"]): sys.exit("test_python: %s: escape_string() differs from the canonical form" % where)
    # the binding's own API, checked on the generated rows (no input of its own): number= maps a lexeme, Error.code is the ABI code of the reference's code name
    seen = []
    for r in rows_sample:
        data = bytes.fromhex(r["input"])
        assert canon(vbm_json.parse(data, number=lambda s: (seen.append(s), Number(s))[1])) == bytes.fromhex(r["canonical"]), "test_python: number= differs from the default on " + r["set"]
    assert seen and all(isinstance(x, str) for x in seen), "test_python: number= was never called with a lexeme"
    assert sorted(codes) == ["depth", "syntax"] and all(isinstance(e, vbm_json.Error) and e.code == {"syntax": 1, "depth": 2}[n] for n, e in codes.items()), codes
    bad = 0
    for r in rows_sample[:500]:   # escape_string on the (arbitrary) input bytes: valid UTF-8 is the literal, anything else JSONSyntaxError (Python's strict decoder decides)
        b = bytes.fromhex(r["input"])
        try: b.decode("utf-8"); valid = True
        except UnicodeDecodeError: valid = False
        if valid: assert vbm_json.escape_string(b) == canon(b.decode("utf-8")), "test_python: escape_string differs from the escape table"
        else:
            try: vbm_json.escape_string(b); sys.exit("test_python: escape_string accepted bytes that are not UTF-8")
            except vbm_json.JSONSyntaxError: bad += 1
    try: vbm_json.escape_string(b"\xff"); sys.exit("test_python: escape_string accepted 0xff")
    except vbm_json.JSONSyntaxError: pass
    print("test_python: %d rows (%s): %d accepted and read back to the canonical form, %d errors with the reference's code" % (rows, ", ".join("%s %d" % kv for kv in sorted(sets.items())), ok, errs))

main()
