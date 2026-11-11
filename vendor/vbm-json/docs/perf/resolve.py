#!/usr/bin/env python3
"""Bin the instruction pointers written by `prof ... sample` into symbols. Usage: resolve.py BINARY SAMPLES [TOP]. Prints percent of samples per symbol, then per PHASE (the table at the bottom: first matching pattern wins) (nm -n of the binary; static link; the first line of SAMPLES is the address of main)."""
import bisect, subprocess, sys, collections
b, s = sys.argv[1], sys.argv[2]; top = int(sys.argv[3]) if len(sys.argv) > 3 else 25
syms = sorted((int(a, 16), n) for a, t, n in (l.split(None, 2) for l in subprocess.run(["nm", "-n", b], capture_output=True, text=True).stdout.splitlines() if len(l.split(None, 2)) == 3) if t in "tTwW")
addrs = [a for a, _ in syms]
rows = open(s).read().split()
base = int(rows[0], 16) - next(a for a, n in syms if n == "main")   # load bias (0 unless PIE)
c = collections.Counter(); tot = 0
for l in rows[1:]:
    ip = int(l, 16) - base; i = bisect.bisect_right(addrs, ip) - 1
    c[syms[i][1] if i >= 0 else "?"] += 1; tot += 1
print(f"{tot} samples")
PH = [("instrumentation (--wrap counters)", r"^__wrap_"), ("parse: string chars (UTF-8 decode, escapes, String.push)", r"strLoop|lean_string_push|Char_ofNat|push_unicode|decodeCharA|decodeUtf8A|lean_string"),
  ("parse: whitespace", r"skipWsA|isWs"), ("parse: number lexemes (digit lists)", r"digitsAcc|parseNumA|parseIntA|parseFracA|parseExpA|digits1A"), ("parse: driver (run loop, stack)", r"LeanJson_run$|byteAt|byteIs|litA|parseKeyA|parseStrA"),
  ("tape: encode (encValue, TapeBuf.node/leaf, ByteArray.push/++)", r"encValue|encList|encMembers|TapeBuf|lean_byte_array|lean_copy_byte|pushWord|setWord"), ("tape: number printing (printInt/printNumber, List.toArray)", r"printInt|printNumber|toArrayAux|lean_array_push|lean_array_mk|lean_list_to_array"),
  ("List.reverse / List.length (parse reverses element lists and digit lists; encode takes xs.length)", r"List_reverse|List_lengthTR"),
  ("allocator: malloc side (lean_alloc_*, mi_malloc, page extend)", r"lean_alloc|mi_malloc|mi_page|_mi_|mi_heap|mi_theap|mi_segment|mi_arena|mi_abandoned"), ("free side: refcount dec, lean_del, mi_free", r"lean_dec_ref|lean_del|lean_free|mi_free|lean_inc"),
  ("outside the binary (libc memcpy/memset/malloc via the shim)", r"^_fini$|^_init$|^\?$")]
import re
for n, k in c.most_common(top): print(f"{100 * k / tot:6.2f}%  {n}")

ph = collections.Counter()
for n, k in c.items():
    for name, pat in PH:
        if re.search(pat, n): ph[name] += k; break
    else: ph["other: " + n] += k
print("-- phases")
for n, k in ph.most_common(): print(f"{100 * k / tot:6.2f}%  {n}")
