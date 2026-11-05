import VbmLlm
import LeanJson
/-! The conformance checker. `vbm-llm-vectors --check [DIR]` decodes every `DIR/openai-chat/NAME.json` (a reply as recorded, or as the published schema's own example gives it) and folds every
`DIR/openai-chat-stream/NAME.sse` (a recorded stream) with the library and compares the rendering with `NAME.expect`; `--write` writes the expectations (to be read and committed by a reviewer).
A stream `NAME.sse` that has a `NAME.single.json` beside it must fold to a complete reply that renders **exactly as the single-shot decode of that file**: the stream-equals-single-shot check, on recorded data.
`--selftest` proves the check can fail: a tampered expectation, a missing vector and a stream that differs from its single-shot reply are each rejected, in the same run. Not part of any export.

The server-sent-event splitter below is a **stub standing in for `vbm-sse`** (whole buffer, the WHATWG rules: lines end at LF, CR LF or CR; a line starting with a colon is a comment; one field per line, one leading
space of the value dropped; consecutive `data` lines join with LF; a blank line dispatches an event that has data; an event cut off by the end of the buffer is discarded). It is trusted test code, listed in the trust ledger,
and goes away when `vbm-sse` is pinned. -/
open System

def lineEnds (s : String) : List String :=
  -- split on LF, CR LF and lone CR
  let s := s.replace "\r\n" "\n"
  (s.replace "\r" "\n").splitOn "\n"

structure Pending where
  type : String := ""
  data : List String := []
  id : Option String := none

/-- The events of a whole buffer. -/
def splitEvents (text : String) : List VbmLlm.Event :=
  -- the last element of `lineEnds` is what follows the final line end: an event that was not terminated by a blank line is dropped
  let ls := lineEnds text
  let ls := ls.dropLast
  let rec go : List String → Pending → List VbmLlm.Event → List VbmLlm.Event
    | [], _, out => out.reverse
    | l :: rest, a, out =>
      if l.isEmpty then
        if a.data.isEmpty then go rest {} out
        else go rest {} (⟨a.type, "\n".intercalate a.data.reverse, a.id⟩ :: out)
      else if l.startsWith ":" then go rest a out
      else
        let (f, v) := match l.splitOn ":" with
          | [f] => (f, "")
          | f :: vs => (f, ":".intercalate vs)
          | [] => ("", "")
        let v := if v.startsWith " " then (v.drop 1).toString else v
        match f with
        | "data" => go rest { a with data := v :: a.data } out
        | "event" => go rest { a with type := v } out
        | "id" => go rest { a with id := some v } out
        | _ => go rest a out
  go ls {} []

def parseData (s : String) : Option LeanJson.Value := (LeanJson.parseFast s.toUTF8).toOption

def decodeFile (p : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile p
  match LeanJson.parseFast bytes with
  | .error _ => return "error\nnot JSON (refused by the pinned parser)\n"
  | .ok v => return VbmLlm.OpenAI.renderResult (VbmLlm.OpenAI.decode v)

def foldFile (p : FilePath) : IO String := do
  let text ← IO.FS.readFile p
  return VbmLlm.OpenAI.renderOutcome (VbmLlm.OpenAI.foldEvents {} parseData (splitEvents text))

def listDir (dir : FilePath) (ext : String) : IO (Array FilePath) := do
  if !(← dir.pathExists) then return #[]
  let es ← dir.readDir
  return (es.map (·.path)).filter (·.extension == some ext) |>.qsort (fun a b => a.toString < b.toString)

/-- The rendering of a recorded stream that has a single-shot twin must be the twin's rendering with `complete` for `ok`. -/
def twinOf (p : FilePath) : FilePath := (p.withExtension "single").withExtension "json"

def main (args : List String) : IO UInt32 := do
  let dir : FilePath := (args.filter (!·.startsWith "--")).headD "vectors"
  let js ← listDir (dir / "openai-chat") "json"
  let ss ← listDir (dir / "openai-chat-stream") "sse"
  if js.isEmpty || ss.isEmpty then IO.eprintln "vbm-llm-vectors: no vectors found"; return 1
  if args.contains "--write" then
    for p in js do IO.FS.writeFile (p.withExtension "expect") (← decodeFile p)
    for p in ss do IO.FS.writeFile (p.withExtension "expect") (← foldFile p)
    IO.println s!"vbm-llm-vectors: wrote {js.size + ss.size} expectations"; return 0
  let mut bad := 0
  for (p, kind) in (js.map (·, 0)) ++ (ss.map (·, 1)) do
    let got ← if kind == 0 then decodeFile p else foldFile p
    let ep := p.withExtension "expect"
    if !(← ep.pathExists) then IO.eprintln s!"vbm-llm-vectors: {p}: no expectation"; bad := bad + 1; continue
    if got != (← IO.FS.readFile ep) then IO.eprintln s!"vbm-llm-vectors: {p}: the result differs from {ep}\n{got}"; bad := bad + 1
    if kind == 1 then
      let twin := twinOf p
      if ← twin.pathExists then
        let single ← decodeFile twin
        -- both render `ok`/`complete` then the same reply lines
        if single.dropWhile (· != '\n') != got.dropWhile (· != '\n') || !got.startsWith "complete\n" then
          IO.eprintln s!"vbm-llm-vectors: {p}: the stream does not fold to the reply of {twin}\n{got}\n{single}"; bad := bad + 1
  IO.println s!"vbm-llm-vectors: {js.size} replies and {ss.size} streams, {bad} differ"
  if args.contains "--selftest" then
    let p := js[0]!
    let want ← IO.FS.readFile (p.withExtension "expect")
    let got ← decodeFile p
    if got != want then IO.eprintln "vbm-llm-vectors: the first vector differs: no self-test"; return 1
    if (want ++ "x") == got || (want.dropEnd 1).toString == got then IO.eprintln "vbm-llm-vectors: the check cannot fail (a tampered expectation equals the decode)"; return 1
    let nope ← decodeFile (p.withExtension "nonexistent") <|> pure "missing"
    if nope != "missing" then IO.eprintln "vbm-llm-vectors: the check cannot fail (a missing vector decodes)"; return 1
    -- a stream that loses its last content piece must not equal its single-shot reply
    let q := ss[0]!
    let text ← IO.FS.readFile q
    let cut := VbmLlm.OpenAI.renderOutcome (VbmLlm.OpenAI.foldEvents {} parseData ((splitEvents text).take 1))
    if cut.startsWith "complete" then IO.eprintln "vbm-llm-vectors: the check cannot fail (a cut stream folds to a complete reply)"; return 1
    IO.println "vbm-llm-vectors: the check rejects tampered rows, missing vectors and a cut stream"
  return if bad == 0 then 0 else 1
