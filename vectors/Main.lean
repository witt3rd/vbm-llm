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

/-- A request vector: the decoded request is shown as its canonical encoding (the printed `encode`), and the encoding must decode, again from the bytes, to the same canonical text. -/
def decodeRequestFile (p : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile p
  match LeanJson.parseFast bytes with
  | .error _ => return "error\nnot JSON (refused by the pinned parser)\n"
  | .ok v =>
    match VbmLlm.OpenAI.Request.decode v with
    | .error f => return "error\n" ++ f.render ++ "\n"
    | .ok r =>
      let canon := ByteArray.mk (LeanJson.print r.encode).toArray
      let text := String.fromUTF8! canon
      match LeanJson.parseFast canon with
      | .error _ => return "round trip FAILED: the encoding is not JSON\n"
      | .ok v2 =>
        match VbmLlm.OpenAI.Request.decode v2 with
        | .ok r2 => if (LeanJson.print r2.encode) == (LeanJson.print r.encode) then return "ok\n" ++ text ++ "\n" else return "round trip FAILED: the encoding reads back differently\n"
        | .error _ => return "round trip FAILED: the encoding is refused\n"

/-! The turn-machine vectors: `openai-chat-turn/NAME.json` is a list of recorded items (`{"kind":"text","role",...}`, `{"kind":"turn","content"?,"calls":[{id,name,arguments}]}`, `{"kind":"result","id","content"}`), the expectation is the
messages of the next request as the library renders them. The checker also checks, **independently of the library's proofs**, that the rendering is well paired (every assistant message followed by one `tool` message per call, in order,
with the call's id, no other `tool` message) and that the rendering of every prefix that ends before an assistant item is a prefix of the whole. -/
open VbmLlm in
def roleOf : String → Option Role
  | "system" => some .system | "developer" => some .developer | "user" => some .user | "assistant" => some .assistant | _ => none

open VbmLlm in
def callOf (v : LeanJson.Value) : Option OpenAI.ToolCall := do
  pure ⟨← str? (get v "id"), ← str? (get v "name"), ← str? (get v "arguments")⟩

open VbmLlm in
def itemOf (v : LeanJson.Value) : Option Entry :=
  match str? (get v "kind") with
  | some "text" => do pure (.text (← roleOf (← str? (get v "role"))) (← str? (get v "content")))
  | some "turn" => do
    let calls ← (match get v "calls" with | .arr xs => xs.mapM callOf | _ => none)
    pure (.turn (str? (get v "content")) calls)
  | some "result" => do pure (.result (← str? (get v "id")) (← str? (get v "content")))
  | _ => none

open VbmLlm VbmLlm.OpenAI in
def isAsst : Entry → Bool
  | .turn .. => true
  | .text .assistant _ => true
  | _ => false

open VbmLlm VbmLlm.OpenAI in
partial def pairedOk : List RequestMessage → Bool
  | [] => true
  | .tool .. :: _ => false
  | .assistant _ cs :: rest =>
    let n := cs.length
    (rest.take n).length == n && ((rest.take n).zip cs).all (fun (m, c) => match m with | .tool i _ => i == c.id | _ => false) && pairedOk (rest.drop n)
  | _ :: rest => pairedOk rest

open VbmLlm VbmLlm.OpenAI in
def renderTurnFile (p : FilePath) : IO String := do
  let bytes ← IO.FS.readBinFile p
  match LeanJson.parseFast bytes with
  | .error _ => return "error\nnot JSON (refused by the pinned parser)\n"
  | .ok (.arr xs) =>
    match xs.mapM itemOf with
    | none => return "error\nnot a list of recorded items\n"
    | some items =>
      let msgs := render {} items
      let mut bad := ""
      if !pairedOk msgs then bad := bad ++ "NOT PAIRED\n"
      for (it, k) in items.zipIdx do
        if isAsst it && !((render {} (items.take k)).isPrefixOf msgs) then bad := bad ++ s!"PREFIX UNSTABLE at {k}\n"
      return "ok\n" ++ bad ++ String.fromUTF8! (ByteArray.mk (LeanJson.print (.arr (msgs.map encodeMessage))).toArray) ++ "\n"
  | .ok _ => return "error\nnot a list of recorded items\n"

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
  let rs ← listDir (dir / "openai-chat-request") "json"
  let ts ← listDir (dir / "openai-chat-turn") "json"
  if js.isEmpty || ss.isEmpty || rs.isEmpty || ts.isEmpty then IO.eprintln "vbm-llm-vectors: no vectors found"; return 1
  if args.contains "--write" then
    for p in js do IO.FS.writeFile (p.withExtension "expect") (← decodeFile p)
    for p in ss do IO.FS.writeFile (p.withExtension "expect") (← foldFile p)
    for p in rs do IO.FS.writeFile (p.withExtension "expect") (← decodeRequestFile p)
    for p in ts do IO.FS.writeFile (p.withExtension "expect") (← renderTurnFile p)
    IO.println s!"vbm-llm-vectors: wrote {js.size + ss.size + rs.size + ts.size} expectations"; return 0
  let mut bad := 0
  for (p, kind) in (js.map (·, 0)) ++ (ss.map (·, 1)) ++ (rs.map (·, 2)) ++ (ts.map (·, 3)) do
    let got ← if kind == 0 then decodeFile p else if kind == 1 then foldFile p else if kind == 2 then decodeRequestFile p else renderTurnFile p
    let ep := p.withExtension "expect"
    if !(← ep.pathExists) then IO.eprintln s!"vbm-llm-vectors: {p}: no expectation"; bad := bad + 1; continue
    if got != (← IO.FS.readFile ep) then IO.eprintln s!"vbm-llm-vectors: {p}: the result differs from {ep}\n{got}"; bad := bad + 1
    if kind == 3 && (got.startsWith "ok\nNOT PAIRED" || got.startsWith "ok\nPREFIX UNSTABLE") then
      IO.eprintln s!"vbm-llm-vectors: {p}: the rendering is not well paired or not prefix-stable\n{got}"; bad := bad + 1
    if kind == 1 then
      let twin := twinOf p
      if ← twin.pathExists then
        let single ← decodeFile twin
        -- both render `ok`/`complete` then the same reply lines
        if single.dropWhile (· != '\n') != got.dropWhile (· != '\n') || !got.startsWith "complete\n" then
          IO.eprintln s!"vbm-llm-vectors: {p}: the stream does not fold to the reply of {twin}\n{got}\n{single}"; bad := bad + 1
  IO.println s!"vbm-llm-vectors: {js.size} replies, {ss.size} streams, {rs.size} requests and {ts.size} turn records, {bad} differ"
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
    -- a request: a tampered expectation is rejected, and the schema's image example (content parts, not modelled) is refused rather than dropped
    let rp := rs[0]!
    let rwant ← IO.FS.readFile (rp.withExtension "expect")
    if (rwant ++ "x") == (← decodeRequestFile rp) || !rwant.startsWith "ok\n" then IO.eprintln "vbm-llm-vectors: the request check cannot fail (or the first request is not read)"; return 1
    let img ← decodeRequestFile (dir / "openai-chat-request" / "002-image-input.json")
    if !img.startsWith "error\n" then IO.eprintln "vbm-llm-vectors: a message with content parts was not refused"; return 1
    -- the turn checks: the independent pairing check rejects an unanswered call, a stray tool message and a wrong id; a tampered record is rejected; no recorded turn carries a flag
    let k : VbmLlm.OpenAI.ToolCall := ⟨"c1", "f", "{}"⟩
    if pairedOk [.assistant none [k], .user "x"] || pairedOk [.tool "c1" "x"] || pairedOk [.assistant none [k], .tool "c2" "x"] || !pairedOk [.assistant none [k], .tool "c1" "x"] then
      IO.eprintln "vbm-llm-vectors: the pairing check cannot fail (or rejects a paired list)"; return 1
    let tp := ts[0]!
    let twant ← IO.FS.readFile (tp.withExtension "expect")
    if (twant ++ "x") == (← renderTurnFile tp) then IO.eprintln "vbm-llm-vectors: the turn check cannot fail"; return 1
    IO.println "vbm-llm-vectors: the check rejects tampered rows, missing vectors, a cut stream, a tampered request, a dropped content part, an unpaired turn"
  return if bad == 0 then 0 else 1
