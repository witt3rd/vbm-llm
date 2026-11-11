// tests/wasm/vbm_json.mjs: the loader for the freestanding wasm32 build of vbm-json (build: scripts/build_wasm.sh). No dependencies; Node's (or any browser's) WebAssembly.
// It moves bytes and reads the tape; what is valid and what a value is, is decided in Lean only (include/vbm_json.h, the boundary never decides).
// The module imports nothing: instantiate with an empty imports object (an import would make instantiation fail, which is the gate).
export const OK = 0, SYNTAX = 1, DEPTH = 2, NOMEM = 3, ARG = 4, INTERNAL = 5;
export const MAX_INPUT = 1 << 30;   // the Lean runtime in the module has no bignums: Nats stay below 2^31 (runtime/rt.c)
const BYTES_STRUCT = 28;            // sizeof(vbm_json_bytes) on wasm32: data, len, block_, block_size_, allocator{ctx,alloc,free}
const TAPE_STRUCT = 36;             // sizeof(vbm_json_tape) on wasm32: words, nwords, text, ntext, block_, block_size_, allocator{ctx,alloc,free}

export async function load(bytes) {
  const { instance } = await WebAssembly.instantiate(bytes, {});
  const x = instance.exports;
  const mem = () => x.memory.buffer;      // re-read after every call: memory.grow detaches the old buffer
  /** Parse `input` (Uint8Array). Returns {code} (not OK: nothing else), or {code: OK, words: BigUint64Array, text: Uint8Array} COPIES of the tape (valid after the next call). */
  function parse(input) {
    if (input.length > MAX_INPUT) return { code: ARG };
    const inp = x.vbm_json_wasm_alloc(Math.max(input.length, 1)), t = x.vbm_json_wasm_alloc(TAPE_STRUCT);
    if (!inp || !t) { if (inp) x.vbm_json_wasm_dealloc(inp); if (t) x.vbm_json_wasm_dealloc(t); return { code: NOMEM }; }
    new Uint8Array(mem(), inp, input.length).set(input);
    const code = x.vbm_json_parse(inp, input.length, 0, t);
    let r = { code };
    if (code === OK) {
      const v = new DataView(mem()), words = v.getUint32(t, true), nwords = v.getUint32(t + 4, true), text = v.getUint32(t + 8, true), ntext = v.getUint32(t + 12, true);
      r = { code, words: new BigUint64Array(mem().slice(words, words + 8 * nwords)), text: new Uint8Array(mem().slice(text, text + ntext)) };
      x.vbm_json_free(t);
    }
    x.vbm_json_wasm_dealloc(inp); x.vbm_json_wasm_dealloc(t);
    return r;
  }
  /** The compact JSON that vbm_json_print_tape writes for the tape of `input` (parsed first, in the module): {code} (the parse code or the print code), or {code: OK, bytes} a COPY. */
  function printed(input) {
    if (input.length > MAX_INPUT) return { code: ARG };
    const inp = x.vbm_json_wasm_alloc(Math.max(input.length, 1)), t = x.vbm_json_wasm_alloc(TAPE_STRUCT), o = x.vbm_json_wasm_alloc(BYTES_STRUCT);
    if (!inp || !t || !o) { for (const p of [inp, t, o]) if (p) x.vbm_json_wasm_dealloc(p); return { code: NOMEM }; }
    new Uint8Array(mem(), inp, input.length).set(input);
    let code = x.vbm_json_parse(inp, input.length, 0, t), r = { code };
    if (code === OK) {
      code = x.vbm_json_print_tape(t, 0, o); r = { code };
      if (code === OK) { const v = new DataView(mem()), d = v.getUint32(o, true), n = v.getUint32(o + 4, true); r = { code, bytes: new Uint8Array(mem().slice(d, d + n)) }; x.vbm_json_bytes_free(o); }
      x.vbm_json_free(t);
    }
    for (const p of [inp, t, o]) x.vbm_json_wasm_dealloc(p);
    return r;
  }
  /** The string literal that vbm_json_escape_string writes for the UTF-8 text `input`: {code} or {code: OK, bytes}. */
  function escaped(input) {
    if (input.length > MAX_INPUT) return { code: ARG };
    const inp = x.vbm_json_wasm_alloc(Math.max(input.length, 1)), o = x.vbm_json_wasm_alloc(BYTES_STRUCT);
    if (!inp || !o) { for (const p of [inp, o]) if (p) x.vbm_json_wasm_dealloc(p); return { code: NOMEM }; }
    new Uint8Array(mem(), inp, input.length).set(input);
    const code = x.vbm_json_escape_string(inp, input.length, 0, o);
    let r = { code };
    if (code === OK) { const v = new DataView(mem()), d = v.getUint32(o, true), n = v.getUint32(o + 4, true); r = { code, bytes: new Uint8Array(mem().slice(d, d + n)) }; x.vbm_json_bytes_free(o); }
    for (const p of [inp, o]) x.vbm_json_wasm_dealloc(p);
    return r;
  }
  return { parse, printed, escaped, live: () => x.vbm_json_wasm_live(), memoryBytes: () => mem().byteLength, exports: x };
}

/** Read a tape back to compact JSON bytes (strict: bounds, subtree sizes, text order); returns Uint8Array or throws. This is a second decoder, counted as boundary and tested. */
export function tapeToCompact({ words, text }) {
  const out = []; let i = 0, cur = 0;
  const put = (s) => { for (const c of s) out.push(c.charCodeAt(0)); };
  const node = (depth) => {
    if (depth > 600 || i + 2 > words.length) throw new Error("tape: bounds");
    const at = i, head = words[i], aux = Number(words[i + 1]), kind = Number(head & 0xffn), len = Number(head >> 8n);
    i += 2;
    switch (kind) {
      case 0: case 1: case 2: if (len || aux) throw new Error("tape: scalar"); put(["null", "false", "true"][kind]); return;
      case 3: case 4: {
        if (aux !== cur || len > text.length || aux > text.length - len) throw new Error("tape: text");
        const s = text.subarray(aux, aux + len); cur += len;
        if (kind === 3) { for (const b of s) out.push(b); return; }
        out.push(0x22);
        for (const c of s) {
          if (c === 0x22) put('\\"'); else if (c === 0x5c) put("\\\\"); else if (c === 8) put("\\b"); else if (c === 12) put("\\f");
          else if (c === 10) put("\\n"); else if (c === 13) put("\\r"); else if (c === 9) put("\\t");
          else if (c < 0x20) put("\\u00" + c.toString(16).padStart(2, "0")); else out.push(c);
        }
        out.push(0x22); return; }
      case 5: case 6:
        if (aux < 2 || aux > words.length - at) throw new Error("tape: subtree");
        out.push(kind === 5 ? 0x5b : 0x7b);
        for (let k = 0; k < len; k++) {
          if (k) out.push(0x2c);
          if (kind === 6) { if (i + 2 > words.length || Number(words[i] & 0xffn) !== 4) throw new Error("tape: key"); node(depth + 1); out.push(0x3a); }
          node(depth + 1);
        }
        out.push(kind === 5 ? 0x5d : 0x7d);
        if (i !== at + aux) throw new Error("tape: subtree size"); return;
      default: throw new Error("tape: kind");
    }
  };
  node(0);
  if (i !== words.length || cur !== text.length) throw new Error("tape: trailing");
  return Uint8Array.from(out);
}
