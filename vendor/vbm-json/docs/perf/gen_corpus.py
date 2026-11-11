#!/usr/bin/env python3
"""Deterministic synthetic corpora for docs/perf/profile.md (stdlib only): small-objects.json and string-heavy.json. Usage: gen_corpus.py OUTDIR"""
import json, random, sys, os
out = sys.argv[1]
r = random.Random(20261104)
# many tiny objects: 60000 records of {"id":N,"ok":bool,"v":N} (short keys, small ints, no strings longer than a few bytes)
small = [{"id": i, "ok": bool(i & 1), "v": r.randrange(1000), "n": None} for i in range(60000)]
# string-heavy: 20000 strings of 20..200 chars; ~25% carry escapes (\n \" \\ \u00e9 and a surrogate pair), ~25% carry multibyte UTF-8
alpha = "abcdefghijklmnopqrstuvwxyz ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-"
def s(i):
    n = r.randrange(20, 200); t = "".join(r.choice(alpha) for _ in range(n))
    if i % 4 == 0: t = t[:n // 2] + '\n"\\\u00e9\U0001F600' + t[n // 2:]
    if i % 4 == 1: t = t[:n // 3] + "\u00fc\u4e2d\u6587\u00e9" + t[n // 3:]
    return t
strs = [{"text": s(i), "lang": "en"} for i in range(20000)]
for name, doc, ea in (("small-objects.json", small, False), ("string-heavy.json", strs, True)):
    with open(os.path.join(out, name), "w", encoding="utf-8") as f:
        f.write(json.dumps(doc, ensure_ascii=ea, separators=(",", ":")))
