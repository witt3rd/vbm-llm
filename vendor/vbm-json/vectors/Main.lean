import LeanJson
/-! The vector generator's executable: `vbm-json-vectors [--n N] [--out DIR]` writes `vectors.jsonl` and `manifest.json` (default N = 4, DIR = `dist`); `--check` runs the rows
against the reference and a negative self-test (a tampered row must be rejected). All content comes from `LeanJson.Vectors` (the reference); this file only does I/O. -/
open LeanJson

structure Case where
  name : String
  input : ByteArray
  expectOk : Bool

def isOk : Except Error Value → Bool | .ok _ => true | .error _ => false

/-- The expected verdict of each file, or an error text: `y_` accept, `n_` reject, `i_` from the table. -/
def expected (table : List (String × Bool)) (name : String) : Except String Bool :=
  if name.startsWith "y_" then .ok true
  else if name.startsWith "n_" then .ok false
  else match table.lookup name with
    | some b => .ok b
    | none => .error s!"{name}: no entry in i-verdicts.txt"

def parseTable (txt : String) : Except String (List (String × Bool)) :=
  (txt.splitOn "\n").foldlM (init := []) fun acc l =>
    if l.isEmpty || l.startsWith "#" then pure acc else
    match l.splitOn " " with
    | n :: v :: r :: _ =>
      if (acc.lookup n).isSome then throw s!"{n}: duplicate entry" else
      if r.isEmpty then throw s!"{n}: no reason" else
      if v == "accept" then pure ((n, true) :: acc) else if v == "reject" then pure ((n, false) :: acc) else throw s!"{n}: verdict must be accept or reject"
    | _ => throw s!"bad line: {l}"

/-- Failures of `cases` against `parseF` and the reference; `flip` inverts every expectation (the negative self-test). -/
def failures (parseF : ByteArray → Except Error Value) (flip : Bool) (cases : List Case) : List String :=
  cases.filterMap fun c =>
    let ref := parse c.input.data.toList
    let fast := parseF c.input
    let want := c.expectOk != flip
    if !sameResult fast ref then some s!"{c.name}: fast and reference disagree"
    else if isOk ref != want then some s!"{c.name}: expected {if want then "accept" else "reject"}, the reference {if isOk ref then "accepts" else "rejects"}"
    else none

/-- Runs the suite in `dir`; returns the process status. -/
def runJts (dir : String) : IO UInt32 := do
  let table ← match parseTable (← IO.FS.readFile (dir ++ "/i-verdicts.txt")) with
    | .ok t => pure t
    | .error e => IO.eprintln s!"jts: i-verdicts.txt: {e}"; return 1
  let files := (← System.FilePath.readDir dir).map (·.fileName) |>.filter (·.endsWith ".json") |>.qsort (· < ·)
  let mut cases : List Case := []
  for f in files do
    match expected table f with
    | .error e => IO.eprintln s!"jts: {e}"; return 1
    | .ok b => cases := cases ++ [{ name := f, input := ← IO.FS.readBinFile (dir ++ "/" ++ f), expectOk := b }]
  let stray := table.filter fun (n, _) => !files.contains n || !n.startsWith "i_"
  if let (n, _) :: _ := stray then IO.eprintln s!"jts: i-verdicts.txt entry without an i_ file: {n}"; return 1
  let count p := (cases.filter fun c => c.name.startsWith p).length
  let bad := failures parseFast false cases
  if let m :: _ := bad then
    IO.eprintln s!"jts: {bad.length} failure(s), the first: {m}"
    return 1
  -- the check can fail: wrong expectations are all caught, and a fast parser that differs from the reference is caught
  if (failures parseFast true cases).length != cases.length then
    IO.eprintln "jts: the check cannot fail (a flipped expectation passed)"; return 1
  if (failures mutantSwapCodes false cases).isEmpty && (failures mutantDropLast false cases).isEmpty then
    IO.eprintln "jts: the differential cannot fail (both mutants agree on every file)"; return 1
  let accepted := (cases.filter fun c => c.name.startsWith "i_" && c.expectOk).length
  IO.println s!"jts: {cases.length} files (y {count "y_"}, n {count "n_"}, i {count "i_"}: {accepted} accepted, {count "i_" - accepted} rejected by policy); all match the expected verdict, the reference and the fast parser agree on every file; flipped expectations and mutants are caught"
  return 0

/-- Set `bignum`: numbers whose VALUE would need a bignum if the parser ever computed with it (long integer, fraction and exponent parts; huge and tiny exponents; negative zero; digit
counts around 2^7, 2^16 and 10^5), valid and invalid, bare and nested. Verdicts and canonical forms come from the reference (`Row.make`). The WASM runtime has no bignum code (T10): a row
that reaches one traps, and the WASM test fails on a trap. -/
def bignumSet : List Bytes :=
  let rep (c : String) (k : Nat) : String := String.ofList (List.replicate k c.front)
  let lens := [19, 20, 21, 39, 40, 400, 4096, 65535, 65536, 100000]
  let big := lens.flatMap fun k =>
    let d := rep "9" k
    let z := "1" ++ rep "0" k
    [d, "-" ++ d, z, d ++ "." ++ d, "-" ++ d ++ "." ++ d ++ "e" ++ d, "0." ++ d, "0." ++ rep "0" k ++ "1", "1e" ++ d, "1E-" ++ d, "1e+" ++ d, "0e" ++ d, "-0e-" ++ d,
     d ++ "e" ++ rep "0" k ++ "1", z ++ ".0", "[" ++ d ++ "," ++ d ++ "]", "{\"" ++ d ++ "\":" ++ d ++ "}",
     -- invalid: long and wrong
     "0" ++ d, d ++ ".", d ++ "e", d ++ "e+", "." ++ d, "-", "-" ++ rep "0" k, d ++ "." ++ d ++ ".", d ++ d.take 1 ++ "x"]
  let small := ["-0", "-0.0", "-0e0", "-0.0e-0", "0e0", "0E+0", "2147483647", "2147483648", "4294967295", "4294967296", "9223372036854775807", "9223372036854775808",
    "18446744073709551615", "18446744073709551616", "-2147483648", "-2147483649", "1e2147483647", "1e2147483648", "1e4294967296", "1e-2147483649", "1e99999999999999999999",
    "1E400", "1e-400", "123456789012345678901234567890", "0.1e1", "1.7976931348623157e308", "1.7976931348623159e309", "5e-324", "2e-325", "-1e-5", "0.000000000000000000000000000001"]
  (big ++ small).map bytesOf

def tamper (r : Row) : Row :=
  { r with result := match r.result with | .ok c => .ok (0x00 :: c) | .error _ => .ok [0x00] }

def main (args : List String) : IO UInt32 := do
  let rec arg (k : String) (d : String) : List String → String
    | a :: v :: rest => if a == k then v else arg k d (v :: rest)
    | _ => d
  let n := (arg "--n" "4" args).toNat?.getD 4
  let out := arg "--out" "dist" args
  let rows := allRows n
  let bad := rows.filter (!·.check)
  if !bad.isEmpty then
    IO.eprintln s!"vectors: {bad.length} row(s) are not consistent with the reference"
    return 1
  -- the check can fail: every tampered row must be rejected
  if rows.any (fun r => (tamper r).check) then
    IO.eprintln "vectors: the row check cannot fail (a tampered row passed)"
    return 1
  -- the byte printer (the compiled code) writes the row's canonical bytes for the value of every accepted row, and a string's literal is `escapeString` of its UTF-8
  let printDiff := rows.filter fun r => match r.result, parse r.input with
    | .ok c, .ok v => (printBytes v).data.toList != c || (match v with | .str t => (escapeString t.toUTF8).data.toList != c | _ => false)
    | _, _ => false
  if let r :: _ := printDiff then
    IO.eprintln s!"vectors: the byte printer differs from the reference printer on {printDiff.length} row(s), the first: {r.json 0}"
    return 1
  -- the fast parser against the reference on every row (verdict, error code and value), and the same check shown able to fail on two mutants
  let diff := disagreements parseFast rows
  if let r :: _ := diff then
    IO.eprintln s!"vectors: the fast parser differs from the reference on {diff.length} row(s), the first: {r.json 0}"
    return 1
  for (name, m) in [("drop-last-byte", mutantDropLast), ("swap-error-codes", mutantSwapCodes)] do
    if (disagreements m rows).isEmpty then
      IO.eprintln s!"vectors: the differential cannot fail (the mutant {name} agrees with the reference on every row)"
      return 1
  -- the fused tape parser against `parseTape` on every row (the same bytes), and the check shown able to fail on three wrong fused parsers
  let tdiff := tapeDisagreements parseTapeFast rows
  if let r :: _ := tdiff then
    IO.eprintln s!"vectors: the fused tape parser differs from parseTape on {tdiff.length} row(s), the first: {r.json 0}"
    return 1
  for (name, m) in [("drop-last-byte", mutantTapeDropLast), ("flip-last-output-byte", mutantTapeLastByte), ("change-status", mutantTapeStatus)] do
    if (tapeDisagreements m rows).isEmpty then
      IO.eprintln s!"vectors: the tape differential cannot fail (the mutant {name} agrees with parseTape on every row)"
      return 1
  -- stack safety: a document 100000 deep is the `depth` code from both parsers (no crash), and a parser without the bound is caught by that very row
  let deep := asArray (List.replicate 100000 0x5B ++ List.replicate 100000 0x5D)
  if !(sameResult (parseFast deep) (.error .depth) && sameResult (parse deep.data.toList) (.error .depth)) then
    IO.eprintln "vectors: a document 100000 deep is not the depth error"; return 1
  if agrees mutantNoBound deep.data.toList || (disagreements mutantNoBound rows).isEmpty then
    IO.eprintln "vectors: the depth check cannot fail (a parser without the nesting bound agrees on the deep rows)"; return 1
  -- pseudo-random inputs over a richer alphabet (the count is `--fuzz N`; a small run is always done)
  let fuzz := (arg "--fuzz" "20000" args).toNat?.getD 20000
  if let some bs := (fuzzInputs 1 fuzz 24).find? (!agrees parseFast ·) then
    IO.eprintln s!"vectors: the fast parser differs from the reference on the random input {hex bs}"
    return 1
  if let some bs := (fuzzMutated 7 fuzz).find? (!agrees parseFast ·) then
    IO.eprintln s!"vectors: the fast parser differs from the reference on the mutated input {hex bs}"
    return 1
  if let some bs := (fuzzInputs 1 fuzz 24).find? (!tapeAgrees parseTapeFast ·) then
    IO.eprintln s!"vectors: the fused tape parser differs from parseTape on the random input {hex bs}"
    return 1
  if let some bs := (fuzzMutated 7 fuzz).find? (!tapeAgrees parseTapeFast ·) then
    IO.eprintln s!"vectors: the fused tape parser differs from parseTape on the mutated input {hex bs}"
    return 1
  -- a long flat array and a long string do not recurse or overflow the stack: the loop is the only repetition
  let big := asArray (bytesOf ("[" ++ ",".intercalate (List.replicate 200000 "0") ++ "]"))
  match parseFast big with
  | .ok (.arr xs) => if xs.length != 200000 then IO.eprintln "vectors: the long array was misread"; return 1
  | _ => IO.eprintln "vectors: the fast parser rejects a long flat array"; return 1
  let long := asArray (bytesOf ("\"" ++ String.ofList (List.replicate 1000000 'a') ++ "\""))
  match parseFast long with
  | .ok (.str s) => if s.length != 1000000 then IO.eprintln "vectors: the long string was misread"; return 1
  | _ => IO.eprintln "vectors: the fast parser rejects a long string"; return 1
  let deepBad := !tapeAgrees parseTapeFast deep.data.toList
  if deepBad then IO.eprintln "vectors: the fused tape parser differs from parseTape on the 100000-deep document"; return 1
  if !tapeAgrees parseTapeFast big.data.toList || !tapeAgrees parseTapeFast long.data.toList then
    IO.eprintln "vectors: the fused tape parser differs from parseTape on the long array or the long string"; return 1
  -- `--corpus DIR`: the same differential on every `*.json` of a directory kept outside the repository (the perf corpora, `docs/perf/profile.md`)
  let corpus := arg "--corpus" "" args
  if corpus != "" then
    let cfiles := (← System.FilePath.readDir corpus).map (·.fileName) |>.filter (·.endsWith ".json") |>.qsort (· < ·)
    for f in cfiles do
      let bytes ← IO.FS.readBinFile (corpus ++ "/" ++ f)
      let ok := tapeAgreesBA parseTapeFast bytes
      IO.println s!"corpus {f}: {bytes.size} bytes, the fused tape parser {if ok then "gives parseTape's bytes" else "DIFFERS from parseTape"}"
      if !ok then return 1
  let jtsDir := arg "--jts" "vectors/jsontestsuite" args
  let jts ← runJts jtsDir
  if jts != 0 then return jts
  if args.contains "--check" then
    IO.println s!"vectors: {rows.length} rows consistent with the reference; the check rejects tampered rows; the byte printer gives the canonical bytes of every accepted row; the fast parser agrees with the reference on every row, and the differential rejects two mutants; the fused tape parser gives parseTape's bytes on every row and the differential rejects three mutants; {fuzz} random and {fuzz} mutated inputs agree"
    return 0
  -- the JSONTestSuite files as rows of set `jts` (the reference's verdict on each file), so every binding and the C ABI test run them too
  let jtsFiles := (← System.FilePath.readDir jtsDir).map (·.fileName) |>.filter (·.endsWith ".json") |>.qsort (· < ·)
  let mut jrows : List Row := []
  for f in jtsFiles do jrows := jrows ++ [Row.make "jts" (← IO.FS.readBinFile (jtsDir ++ "/" ++ f)).data.toList]
  let rows := rows ++ jrows ++ bignumSet.map (Row.make "bignum")
  let lines := (rows.zipIdx).map fun (r, i) => r.json i
  let body := "\n".intercalate lines ++ "\n"
  IO.FS.createDirAll out
  IO.FS.writeFile (out ++ "/vectors.jsonl") body
  let count (s : String) := (rows.filter (·.set == s)).length
  let sets := ["enum", "number", "escape", "utf8", "depth", "misc", "jts", "bignum"].map fun s => s!"\"{s}\":{count s}"
  IO.FS.writeFile (out ++ "/manifest.json")
    s!"\{\"format\":\"vbm-json-vectors-1\",\"maxDepth\":{maxDepth},\"enumN\":{n},\"rows\":{rows.length},\"sets\":\{{",".intercalate sets}},\"fnv1a64\":\"{hex64 (fnv1a body.toUTF8)}\",\"generator\":\"reference\"}\n"
  IO.println s!"vectors: {rows.length} rows -> {out}/vectors.jsonl"
  return 0
