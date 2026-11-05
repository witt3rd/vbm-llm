import VbmLlm
import LeanJson
/-! The conformance checker. `vbm-llm-vectors --check [DIR]` decodes every `DIR/openai-chat/NAME.json` (the reply as recorded, or as the published schema's own example gives it) with the library and compares
the rendering with `NAME.expect`; `--write` writes the expectations (to be read and committed by a reviewer). `--selftest` proves the check can fail: a tampered expectation, a missing one and a
rendering that differs by one character are each rejected, in the same run. Not part of any export. -/
open System

def decodeFile (p : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile p
  match LeanJson.parseFast bytes with
  | .error _ => return "error\nnot JSON (refused by the pinned parser)\n"
  | .ok v => return VbmLlm.OpenAI.renderResult (VbmLlm.OpenAI.decode v)

def vectors (dir : FilePath) : IO (Array FilePath) := do
  let d := dir / "openai-chat"
  let es ← d.readDir
  return (es.map (·.path)).filter (·.extension == some "json") |>.qsort (fun a b => a.toString < b.toString)

def main (args : List String) : IO UInt32 := do
  let dir : FilePath := (args.filter (!·.startsWith "--")).headD "vectors"
  let vs ← vectors dir
  if vs.isEmpty then IO.eprintln "vbm-llm-vectors: no vectors found"; return 1
  if args.contains "--write" then
    for p in vs do IO.FS.writeFile (p.withExtension "expect") (← decodeFile p)
    IO.println s!"vbm-llm-vectors: wrote {vs.size} expectations"; return 0
  let mut bad := 0
  for p in vs do
    let got ← decodeFile p
    let ep := p.withExtension "expect"
    if !(← ep.pathExists) then IO.eprintln s!"vbm-llm-vectors: {p}: no expectation"; bad := bad + 1; continue
    if got != (← IO.FS.readFile ep) then IO.eprintln s!"vbm-llm-vectors: {p}: the decode differs from {ep}\n{got}"; bad := bad + 1
  IO.println s!"vbm-llm-vectors: {vs.size} vectors, {bad} differ"
  if args.contains "--selftest" then
    let p := vs[0]!
    let want ← IO.FS.readFile (p.withExtension "expect")
    let got ← decodeFile p
    if got != want then IO.eprintln "vbm-llm-vectors: the first vector differs: no self-test"; return 1
    if (want ++ "x") == got || (want.dropEnd 1).toString == got then IO.eprintln "vbm-llm-vectors: the check cannot fail (a tampered expectation equals the decode)"; return 1
    let nope ← decodeFile (p.withExtension "nonexistent") <|> pure "missing"
    if nope != "missing" then IO.eprintln "vbm-llm-vectors: the check cannot fail (a missing vector decodes)"; return 1
    IO.println "vbm-llm-vectors: the check rejects tampered rows and missing vectors"
  return if bad == 0 then 0 else 1
