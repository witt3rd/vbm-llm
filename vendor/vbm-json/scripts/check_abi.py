#!/usr/bin/env python3
"""Tier 1: the ABI description (abi/vbm_json.abi.json) and the C header (include/vbm_json.h) must agree: ABI version, the kind and error enums, every struct field, every function
prototype, the tape head layout; and the kind numbers must equal those of LeanJson/Tape.lean. Usage: check_abi.py [--selftest]. With --selftest it also shows the check can fail:
each of a set of drifted headers (and one drifted description) must be rejected. Exit 1 on any disagreement."""
import json, re, sys

def strip_comments(t):
    t = re.sub(r"/\*.*?\*/", "", t, flags=re.S)
    return "\n".join(l for l in t.splitlines() if not l.lstrip().startswith("#"))

def ws(s):  # whitespace removed: the comparison is of tokens, not of layout
    return re.sub(r"\s+", "", s)

def parse_header(raw):
    """-> dict(version, enums=[{NAME: value}], structs={name: [decl]}, funcs={name: text})"""
    h = {"version": None, "enums": [], "structs": {}, "funcs": {}}
    m = re.search(r"#define\s+VBM_JSON_ABI_VERSION\s+(\d+)u?", raw)
    h["version"] = int(m.group(1)) if m else None
    t = strip_comments(raw)
    for body in re.findall(r"enum\s*\{(.*?)\}\s*;", t, flags=re.S):
        d = {}
        for item in body.split(","):
            if item.strip():
                k, _, v = item.partition("=")
                d[k.strip()] = int(v.strip(), 0)
        h["enums"].append(d)
    t = re.sub(r"enum\s*\{.*?\}\s*;", "", t, flags=re.S)
    def struct(m):
        h["structs"][m.group(2)] = [ws(d) for d in m.group(1).split(";") if d.strip()]
        return ""
    t = re.sub(r"typedef\s+struct\s+\w+\s*\{(.*?)\}\s*(\w+)\s*;", lambda m: struct(m), t, flags=re.S)
    for st in t.split(";"):
        st = st.strip()
        m = re.match(r'^(?:extern\s*"C"\s*\{\s*)?(.*?\b(vbm_json_\w+)\s*\(.*\))$', st, flags=re.S)
        if m and not st.startswith("typedef"):
            h["funcs"][m.group(2)] = ws(m.group(1))
    return h

def lean_kinds(lean):
    return {m.group(1): int(m.group(2)) for m in re.finditer(r"^def kind(\w+) : Nat := (\d+)$", lean, flags=re.M)}

def check(header, desc, lean):
    """-> list of disagreements (empty: they agree)."""
    bad = []
    h = parse_header(header)
    if h["version"] != desc["abi_version"]:
        bad.append(f"ABI version: header {h['version']} vs description {desc['abi_version']}")
    want = [{"VBM_JSON_" + k["name"]: k["value"] for k in desc[g]} for g in ("kinds", "errors")]
    if h["enums"] != want:
        bad.append(f"enums (kinds, then result codes): header {h['enums']} vs description {want}")
    hs = h["structs"]
    if sorted(hs) != sorted(s["name"] for s in desc["structs"]):
        bad.append(f"structs: header {sorted(hs)} vs description {sorted(s['name'] for s in desc['structs'])}")
    for s in desc["structs"]:
        if hs.get(s["name"]) != [ws(f["c"]) for f in s["fields"]]:
            bad.append(f"struct {s['name']}: header {hs.get(s['name'])} vs description {[ws(f['c']) for f in s['fields']]}")
        for f in s["fields"]:
            if not re.search(r"\b%s\b" % re.escape(f["name"]), f["c"]):
                bad.append(f"struct {s['name']}: field name {f['name']} is not in its C text")
    hf = h["funcs"]
    if sorted(hf) != sorted(f["name"] for f in desc["functions"]):
        bad.append(f"functions: header {sorted(hf)} vs description {sorted(f['name'] for f in desc['functions'])}")
    for f in desc["functions"]:
        if hf.get(f["name"]) != ws(f["c"]):
            bad.append(f"function {f['name']}: header {hf.get(f['name'])} vs description {ws(f['c'])}")
        names = re.findall(r"(\w+)\s*(?:,|$)", f["c"].split("(", 1)[1].rstrip(")"))
        if names != [p["name"] for p in f["params"]]:
            bad.append(f"function {f['name']}: parameter names {names} vs {[p['name'] for p in f['params']]}")
    t = desc["tape"]
    if "head = kind | len << %d" % t["len_shift"] not in header or t["head"] != "kind | len << %d" % t["len_shift"] or t["kind_bits"] != t["len_shift"]:
        bad.append("tape head layout: the header does not say 'head = kind | len << %d'" % t["len_shift"])
    if "little-endian u64 words" not in header or t["word_bytes"] != 8 or t["endian"] != "little" or t["node_words"] != 2:
        bad.append("tape words: the header does not say little-endian u64 words, two per node")
    lk = lean_kinds(lean)
    wk = {k["name"].capitalize(): k["value"] for k in desc["kinds"]}
    wk = {{"Number": "Num", "String": "Str", "Array": "Arr", "Object": "Obj"}.get(k, k): v for k, v in wk.items()}
    if lk != wk:
        bad.append(f"kinds: LeanJson/Tape.lean {lk} vs description {wk}")
    return bad

def selftest(header, desc, lean):
    mutants = {
        "an enumerator value changed": lambda h, d, l: (h.replace("VBM_JSON_DEPTH = 2", "VBM_JSON_DEPTH = 7"), d, l),
        "a result code added": lambda h, d, l: (h.replace("VBM_JSON_INTERNAL = 5 }", "VBM_JSON_INTERNAL = 5, VBM_JSON_X = 6 }"), d, l),
        "the ABI version bumped": lambda h, d, l: (h.replace("VBM_JSON_ABI_VERSION 1u", "VBM_JSON_ABI_VERSION 2u"), d, l),
        "a parameter retyped": lambda h, d, l: (h.replace("size_t len,", "uint32_t len,"), d, l),
        "a parameter renamed": lambda h, d, l: (h.replace("const uint8_t *buf,", "const uint8_t *data,"), d, l),
        "a function added": lambda h, d, l: (h.replace("#ifdef __cplusplus\n}", "int vbm_json_extra(int x);\n#ifdef __cplusplus\n}"), d, l),
        "a function removed": lambda h, d, l: (h.replace("void vbm_json_free(vbm_json_tape *tape);", ""), d, l),
        "a struct field retyped": lambda h, d, l: (h.replace("size_t nwords;", "uint32_t nwords;"), d, l),
        "a struct field reordered": lambda h, d, l: (h.replace("const uint8_t *text;   size_t ntext;", "size_t ntext; const uint8_t *text;"), d, l),
        "the tape head layout changed": lambda h, d, l: (h.replace("head = kind | len << 8", "head = kind | len << 16"), d, l),
        "the description drifted (a kind value)": lambda h, d, l: (h, json.loads(json.dumps(d).replace('"STRING", "value": 4', '"STRING", "value": 9')), l),
        "the description drifted (a field type text)": lambda h, d, l: (h, json.loads(json.dumps(d).replace("size_t ntext", "size_t ntext2")), l),
        "Tape.lean kind numbers drifted": lambda h, d, l: (h, d, l.replace("def kindArr : Nat := 5", "def kindArr : Nat := 8")),
    }
    for name, f in mutants.items():
        h2, d2, l2 = f(header, desc, lean)
        if (h2, d2, l2) == (header, desc, lean):
            sys.exit(f"check_abi: self-test: the mutation '{name}' changed nothing")
        if not check(h2, d2, l2):
            sys.exit(f"check_abi: self-test: '{name}' was NOT rejected (the check cannot fail)")
    return len(mutants)

def main():
    header = open("include/vbm_json.h").read()
    desc = json.load(open("abi/vbm_json.abi.json"))
    lean = open("LeanJson/Tape.lean").read()
    bad = check(header, desc, lean)
    if bad:
        print("check_abi: the header and the ABI description disagree:", file=sys.stderr)
        for b in bad: print("  " + b, file=sys.stderr)
        sys.exit(1)
    n = selftest(header, desc, lean) if "--selftest" in sys.argv else 0
    print("check_abi: ok: header, description and Tape.lean agree (%d functions, %d structs, %d kinds, %d result codes)%s" % (
        len(desc["functions"]), len(desc["structs"]), len(desc["kinds"]), len(desc["errors"]),
        "; %d drifted variants each rejected" % n if n else ""))

if __name__ == "__main__":
    main()
