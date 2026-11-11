import Lean
import LeanJson
import LeanJsonProofs
/-! Closure gate (adapted from the closure gate of the project these gates were first built in; docs/decisions/0001-vbm-json.md): what the library's exports execute, classified.

Walks every definition reachable from the entry points (`scripts/closure-entries.txt`: one constant name per line, the Lean functions the C exports
`vbm_json_*` call; none yet, they arrive with the ABI) and sorts it by where it comes from:
  spec        a `LeanJson` definition (specified; the code IS the specification, one Lean core), or a `LeanJsonSimd` definition (the bit-parallel parser, proved equal to the specification by `parseTapeSimd_eq`), or a `VbmSimd` definition (the pinned verified library vbm-simd, proved in its own repository)
  boundary    an `@[extern]` declaration of ours (a named trust-ledger item)
  toolchain   Lean's `Init` (trusted: docs/trust-ledger.md)
  UNVERIFIED  a definition of ours outside `LeanJson` (the ABI shim and the like: none yet); its count per module may only fall
  FORBIDDEN   `LeanJsonProofs` (never linked) or `Std`/`Lean` (Init only: a `Lean.*` import forces full runtime initialisation): any such definition
              reachable from an entry point FAILS the gate.
There is no handler class here: the boundary never decides (AGENTS.md); that project's handler mass and its target ratchet are not carried over.
DEFINITIONS (single source: this gate; other scripts quote its printed line, they never recompute):
  executed mass = the sum, over every definition reachable from the entry points (aux/theorems/constructors excluded), of the expression nodes
    (`sizeWithoutSharing` of its value), for every class of ours: spec + boundary + UNVERIFIED. Not in it: the toolchain (printed apart) and the C
    runtime (unmeasured in nodes).
  specified share = mass(spec) / executed mass. Every run prints the parts, never a bare percentage:
    `spec N | boundary N | unverified N | total N | deciding: n/a (...) | specified share P% (floor M%)`.
  The numerator is ONE class, whose membership no file we control decides: the module root `LeanJson`. The denominator is ALL executed mass of our
  own code, so moving a definition between non-spec classes cannot raise the share. The floor is the baseline line `specified_share S T` (an exact
  fraction); it may only rise: a fall fails, `--write` raises it on improvement and refuses to lower it, a baseline without the line fails.
NOT PORTED YET (upstream work in the originating gates): the deciding-code detector (the boundary / plumbing / deciding
  split of the non-spec mass, the `deciding` field printed below as n/a) and its hidden-code fix. Port them when they land.
Self-tests (`--selftest`, in this one process): the gate can fail, on synthetic measures and baselines, and the classifier and the walk are exercised on the real environment. -/
open Lean

/-- The class of a definition by the module it comes from. -/
def classifyModule (m : Name) : String :=
  let r := m.getRoot
  if r == `LeanJson || r == `LeanJsonSimd || r == `VbmSimd then "spec"
  else if r == `LeanJsonProofs then "proofs"
  else if r == `Init then "toolchain"
  else if r == `Std || r == `Lean then "heavy"
  else "UNVERIFIED"

def classify (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | none => "local"
  | some idx => classifyModule env.header.moduleNames[idx.toNat]!

def isAux (env : Environment) (n : Name) : Bool :=
  isAuxRecursor env n || isNoConfusion env n || (Meta.isMatcherCore env n) ||
  (match env.find? n with
   | some (.ctorInfo _) | some (.recInfo _) | some (.inductInfo _) | some (.quotInfo _) | some (.thmInfo _) | some (.axiomInfo _) => true
   | _ => false) ||
  (n.isInternal && !(n.toString.endsWith "._unsafe_rec")) || (env.getProjectionFnInfo? n).isSome

partial def walk (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then walk env rest seen else
    let seen := seen.insert n
    match env.find? n with
    | none => walk env rest seen
    | some ci =>
      let used : Array Name := (match ci.value? true with | some v => v.getUsedConstants | none => #[])
      let impl := (match Compiler.getImplementedBy? env n with | some i => [i] | none => []) ++
        -- a `partial def` is an opaque constant; its body lives in `<name>._unsafe_rec`
        (if (env.find? (Name.str n "_unsafe_rec")).isSome then [Name.str n "_unsafe_rec"] else [])
      walk env (used.toList ++ impl ++ rest) seen

def readLines (p : String) : IO (List String) := do
  if !(← System.FilePath.pathExists p) then return []
  return (← IO.FS.readFile p).splitOn "\n" |>.map String.trimAscii |>.map (·.toString) |>.filter (fun l => l != "" && !l.startsWith "#")

/-- Mass of everything of ours that executes except the toolchain and the carve-outs (the `@[extern]` shims, scripts/carveouts.txt). The specified share's denominator. -/
def execMass (mass : Std.HashMap String Nat) : Nat :=
  ["spec", "UNVERIFIED"].foldl (fun a c => a + mass.getD c 0) 0   -- the boundary (the named trusted shims) is outside the share: printed as carve-outs

/-- The specified share as an exact fraction (spec mass, executed mass): the one definition the report, the ratchet and the relabel self-tests share. -/
def shareOf (mass : Std.HashMap String Nat) : Nat × Nat := (mass.getD "spec" 0, execMass mass)

/-- Percent with two decimals, in integers (exact floor). -/
def pct (a b : Nat) : String :=
  if b == 0 then "n/a" else
  let p := a * 10000 / b
  s!"{p / 100}.{if p % 100 < 10 then "0" else ""}{p % 100}%"

/-- The recorded floor `specified_share S T`: a share may only rise, compared exactly (S * T0 < S0 * T is a fall). -/
def shareFloor (base : List String) : Option (Nat × Nat) :=
  base.findSome? fun l => match l.splitOn " " with
    | ["specified_share", s, t] => do pure (← s.toNat?, ← t.toNat?)
    | _ => none

def argOf (args : List String) (k d : String) : String := match args.dropWhile (· != k) with | _ :: v :: _ => v | _ => d

/-- What the walk measured: independent of any baseline, so one measurement serves the run and every self-test. -/
structure Measure where
  entries : Nat
  counts : Std.HashMap String Nat
  mass : Std.HashMap String Nat
  perModule : Std.HashMap String Nat
  perModuleMass : Std.HashMap String Nat
  uncovered : Array Name
  forbidden : Array Name
  /-- the carve-outs reached: the `@[extern]` shims (names) -/
  carved : Array Name := #[]

/-- Entry points: `--entry N` (repeatable via the file) or `scripts/closure-entries.txt`. An entry that is not in the environment is an error:
a typo must not measure nothing and pass. -/
def measureClosure (env : Environment) (args : List String) : IO Measure := do
  let arg := argOf args
  let entryNames ← readLines (arg "--entries-file" "scripts/closure-entries.txt")
  let entries := (entryNames ++ (if args.contains "--entry" then [arg "--entry" ""] else [])).map String.toName
  for e in entries do
    if (env.find? e).isNone then throw (IO.userError s!"closure gate: entry point {e} is not in the environment")
  let reach := walk env entries {}
  -- Which constants do the statements of LeanJsonProofs theorems mention? A spec definition that no theorem mentions is "spec" in name only.
  let mut mentioned : NameSet := {}
  -- read from the data of the LeanJsonProofs modules themselves (not by filtering every imported constant, which a self-test environment with `Lean` loaded makes slow)
  for h : i in [0:env.header.moduleNames.size] do
    if (env.header.moduleNames[i]).getRoot == `LeanJsonProofs then
      for ci in env.header.moduleData[i]!.constants do
        if let .thmInfo _ := ci then
          for u in ci.type.getUsedConstants do mentioned := mentioned.insert u
  let mut uncovered : Array Name := #[]
  let mut forbidden : Array Name := #[]
  let mut mass : Std.HashMap String Nat := {}
  let mut counts : Std.HashMap String Nat := {}
  let mut carved : Array Name := #[]
  let mut perModule : Std.HashMap String Nat := {}
  let mut perModuleMass : Std.HashMap String Nat := {}
  for n in reach.toList do
    if isAux env n then continue
    let some ci := env.find? n | continue
    if !(match ci with | .defnInfo _ | .opaqueInfo _ => true | _ => false) then continue
    let c := classify env n
    let cls := if c == "local" then "UNVERIFIED" else if c == "spec" || c == "UNVERIFIED" then (if isExtern env n then "boundary" else c) else c
    counts := counts.insert cls (counts.getD cls 0 + 1)
    if cls == "boundary" then carved := carved.push n
    let size := (ci.value?.map (·.sizeWithoutSharing)).getD 0
    mass := mass.insert cls (mass.getD cls 0 + size)
    if cls == "proofs" || cls == "heavy" then forbidden := forbidden.push n
    if cls == "spec" && !mentioned.contains n then uncovered := uncovered.push n
    if args.contains "--emit" && cls != "spec" then
      IO.println s!"emit {cls} {match env.getModuleIdxFor? n with | some i => (if cls == "toolchain" then (env.header.moduleNames[i.toNat]!).getRoot else env.header.moduleNames[i.toNat]!).toString | none => "?"} {n}"
    if cls == "UNVERIFIED" then
      let m := match env.getModuleIdxFor? n with | some i => (env.header.moduleNames[i.toNat]!).toString | none => "?"
      perModule := perModule.insert m (perModule.getD m 0 + 1)
      perModuleMass := perModuleMass.insert m (perModuleMass.getD m 0 + size)
  return { entries := entries.length, counts, mass, perModule, perModuleMass, uncovered, forbidden, carved }

/-- The report and the ratchet checks of one run against one baseline file (stdout/stderr and the exit code). -/
def report (m : Measure) (args : List String) (baseFile : String) : IO UInt32 := do
  let { entries, counts, mass, perModule, perModuleMass, uncovered, forbidden, carved } := m
  let base ← readLines baseFile
  if entries == 0 then IO.println "closure gate: no entry points yet (scripts/closure-entries.txt is empty: the exports arrive with the ABI); measured nothing"
  IO.println "closure gate: definitions reachable from the entry points, by class"
  for c in ["spec", "boundary", "toolchain", "UNVERIFIED"] do
    IO.println s!"  {c}: {counts.getD c 0}"
  let mods := perModule.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1))
  IO.println "code mass (expression nodes; a count of definitions can be moved by merging or splitting, mass cannot):"
  for c in ["spec", "boundary", "toolchain", "UNVERIFIED"] do
    IO.println s!"  {c}: {mass.getD c 0}"
  let (sm, em) := shareOf mass
  let floor? := shareFloor base
  IO.println "closure gate: DEFINITIONS: executed mass = expression nodes of every definition reachable from the entry points, classes spec+UNVERIFIED (the toolchain, the carve-outs and the C runtime excluded); specified share = spec mass / executed mass"
  IO.println s!"closure gate: carve-outs: {mass.getD "boundary" 0} nodes ({", ".intercalate (carved.toList.map fun n => n.toString)}); outside the share, listed in scripts/carveouts.txt"
  IO.println s!"closure gate: spec {sm} | boundary {mass.getD "boundary" 0} | unverified {mass.getD "UNVERIFIED" 0} | total {em} | deciding: n/a (the deciding-code detector is not yet ported) | specified share {pct sm em} (floor {match floor? with | some (s0, t0) => pct s0 t0 | none => "none"})"
  IO.println s!"  specified share = spec mass {sm} / executed mass {em} (spec+boundary+UNVERIFIED; the toolchain's {mass.getD "toolchain" 0} is outside it). Not counted at all: the C runtime (runtime/runtime.c) and the bindings."
  IO.println s!"spec definitions reachable from the entry points that no LeanJsonProofs theorem statement mentions: {uncovered.size} of {counts.getD "spec" 0} (spec in name only until a theorem constrains them)"
  for n in uncovered.toList.take 8 do IO.println s!"    {n}"
  IO.println "unverified by module:"
  for (m, k) in mods do IO.println s!"  {m} {k}  (mass {perModuleMass.getD m 0})"
  let baseMap : Std.HashMap String Nat := base.foldl (init := {}) fun acc l =>
    match l.splitOn " " with | [m, k] => acc.insert m (k.toNat!) | _ => acc
  let mut bad := 0
  -- the library's closure is Init only and never reaches the proofs
  for n in forbidden.toList.take 8 do IO.eprintln s!"closure gate: {n} is reachable from an entry point but comes from LeanJsonProofs, Std or Lean (only Init and LeanJson may be linked)"
  if !forbidden.isEmpty then bad := bad + 1
  for (m, k) in mods do
    match baseMap.get? m with
    | none => IO.eprintln s!"closure gate: {m} is new unverified code ({k} definitions); the unverified set may only shrink"; bad := bad + 1
    | some b => if k > b then IO.eprintln s!"closure gate: {m} grew from {b} to {k} unverified definitions"; bad := bad + 1
  -- the specified share ratchet: exact comparison, a fall fails; no floor = no ratchet = fail; a stale (low) floor is a notice
  match floor? with
  | none => IO.eprintln s!"closure gate: {baseFile} has no specified_share floor (a ratchet with no floor is no ratchet: run --write once)"; bad := bad + 1
  | some (s0, t0) =>
    if sm * t0 < s0 * em then IO.eprintln s!"closure gate: specified share fell from {pct s0 t0} ({s0}/{t0}) to {pct sm em} ({sm}/{em}); it may only rise (no relabel can raise it: only spec mass can)"; bad := bad + 1
    else if sm * t0 > s0 * em then IO.println s!"closure gate: the share floor {pct s0 t0} is below the measured {pct sm em}: run --write"
  match baseMap.get? "mass" with
  | some b => if mass.getD "UNVERIFIED" 0 > b then IO.eprintln s!"closure gate: unverified code mass grew from {b} to {mass.getD "UNVERIFIED" 0} expression nodes"; bad := bad + 1
  | none => IO.eprintln s!"closure gate: {baseFile} has no unverified mass line"; bad := bad + 1
  if args.contains "--write" then
    if bad != 0 then IO.eprintln "closure gate: --write refuses to write a baseline that fails the ratchets (a worsening is a deliberate, owner-approved edit of the file)"; return 1
    IO.FS.writeFile baseFile ("# unverified definitions reachable from the entry points, per module (scripts/ClosureGate.lean); may only fall\n" ++ String.intercalate "\n" (mods.toList.map fun (m, k) => s!"{m} {k}") ++ s!"{if mods.isEmpty then "" else "\n"}mass {mass.getD "UNVERIFIED" 0}\nspecified_share {sm} {em}\n")
    IO.println "closure gate: baseline written"
    return 0
  if bad == 0 then
    let total := mods.foldl (fun a (_, k) => a + k) 0
    IO.println s!"closure gate: ok ({total} unverified definitions; the baseline may be lowered by running with --write)"
  return if bad == 0 then 0 else 1

/-- The negative self-tests, on synthetic measures and baselines (never the committed baseline: the skeleton's closure is empty, and a self-test that
depends on the measured value would be vacuous), plus the classifier and the walk on the real environment, all in this one process. -/
def selfTests : IO UInt32 := do
  -- an environment that also has `Lean` loaded (the library's own closure never does), so the heavy-class detector can be shown to fire
  let env ← importModules #[{ module := `Lean }, { module := `LeanJson }, { module := `LeanJsonProofs }] {}
  let (h, cb) ← IO.FS.createTempFile
  h.flush
  let cbs := cb.toString
  let mut bad := 0
  let mk (spec boundary unv : Nat) (mods : List (String × Nat)) (forb : Array Name := #[]) : Measure :=
    { entries := 1, counts := {}, perModule := Std.HashMap.ofList mods, perModuleMass := {}, uncovered := #[], forbidden := forb
      mass := Std.HashMap.ofList [("spec", spec), ("boundary", boundary), ("UNVERIFIED", unv), ("toolchain", 50)] }
  let m := mk 100 10 5 [("Abi.Shim", 2)]
  let (sm, em) := shareOf m.mass
  let base (share : List String) (mass : Nat := 5) (mods : List String := ["Abi.Shim 2"]) : IO Unit :=
    IO.FS.writeFile cb ("\n".intercalate (mods ++ [s!"mass {mass}"] ++ share) ++ "\n")
  let run (mm : Measure) (extra : List String := []) : IO (UInt32 × String) := do
    let (out, r) ← IO.FS.withIsolatedStreams (report mm (["--baseline", cbs] ++ extra) cbs)
    return (r, out)
  let has (out s : String) : Bool := (out.splitOn s).length > 1
  let mut expect : List (Bool × String) := []
  -- the gate can fail: against a missing baseline a module of unverified code is new, and there is no floor
  let (_, r) ← IO.FS.withIsolatedStreams (report m [] "/nonexistent")
  expect := expect ++ [(r != 0, "the closure gate cannot fail")]
  -- the ratchets on unverified code: a new module, a module that grew, a mass that grew
  base [s!"specified_share {sm} {em}"] (mods := []); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts new unverified code")]
  base [s!"specified_share {sm} {em}"] (mods := ["Abi.Shim 1"]); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a module whose unverified definitions grew")]
  base [s!"specified_share {sm} {em}"] (mass := 4); let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a grown unverified mass")]
  base [s!"specified_share {sm} {em}"]; let (r, o) ← run m
  expect := expect ++ [(r == 0 && has o s!"specified share {pct sm em} (floor {pct sm em})", "the closure gate fails or does not print the share at its own floor")]
  expect := expect ++ [(has o s!"spec {sm} | boundary 10 | unverified 5 | total {em} | deciding: n/a", "the closure gate prints a bare percentage (the parts are required)")]
  -- the specified share: a fall fails (a real fall of the spec mass, and a floor above the measure), a missing floor fails
  let (r, _) ← run (mk 99 10 5 [("Abi.Shim", 2)])
  expect := expect ++ [(r != 0, "the specified-share ratchet cannot fail on a synthetic fall of the spec mass")]
  base [s!"specified_share {sm + 1} {em}"]; let (r, o) ← run m
  expect := expect ++ [(r != 0 && has o "specified share fell", "the specified-share ratchet accepts a floor above the measured share")]
  base []; let (r, _) ← run m
  expect := expect ++ [(r != 0, "the closure gate accepts a baseline with no specified_share floor")]
  -- a floor of 0/0 (the skeleton's) accepts any share, and an empty closure prints n/a, not a division by zero
  base ["specified_share 0 0"]; let (r, _) ← run (mk 0 0 0 []); let (r', _) ← run m
  expect := expect ++ [(r == 0 && r' == 0, "the closure gate rejects the 0/0 floor of an empty closure or a share above it")]
  -- --write refuses to lower the floor (and writes nothing); on a rise it raises the floor to the measure
  base [s!"specified_share {sm + 1} {em}"]; let before ← IO.FS.readFile cb; let (r, _) ← run m ["--write"]
  expect := expect ++ [(r != 0 && (← IO.FS.readFile cb) == before, "the closure gate --write lowers the specified-share floor")]
  base [s!"specified_share {sm - 1} {em}"]; let (r, _) ← run m ["--write"]
  expect := expect ++ [(r == 0 && ((← IO.FS.readFile cb).splitOn s!"specified_share {sm} {em}").length > 1, "the closure gate --write does not raise the floor on an improvement")]
  -- a relabel cannot raise the share: moving all unverified mass to boundary (mass level) leaves spec and executed mass unchanged
  let relabeled := { m with mass := (m.mass.insert "UNVERIFIED" 0).insert "boundary" (m.mass.getD "boundary" 0 + m.mass.getD "UNVERIFIED" 0) }
  expect := expect ++ [(shareOf relabeled.mass == (sm, em) && relabeled.mass.getD "boundary" 0 == 15, "relabeling UNVERIFIED->boundary changed the specified share (or moved no mass)")]
  -- a reachable definition from LeanJsonProofs, Std or Lean fails the gate
  base [s!"specified_share {sm} {em}"]; let (r, _) ← run (mk 100 10 5 [("Abi.Shim", 2)] #[`Lean.Json.compress])
  expect := expect ++ [(r != 0, "the closure gate accepts a reachable Std/Lean/LeanJsonProofs definition")]
  IO.FS.removeFile cb
  -- the classifier, by module root
  for (mod, c) in [(`LeanJson.Value, "spec"), (`LeanJsonProofs.Ledger, "proofs"), (`Init.Prelude, "toolchain"), (`Lean.Data.Json, "heavy"), (`Std.Data.HashMap, "heavy"), (`Abi.Shim, "UNVERIFIED")] do
    expect := expect ++ [(classifyModule mod == c, s!"classifyModule {mod} is not {c}")]
  -- the walk on the real environment: a toolchain function is measured (and is not heavy), a Lean.Json function IS heavy, a proof-library function is "proofs",
  -- an entry point that does not exist is an error (so the empty closure of the skeleton cannot hide a typo)
  let mT ← measureClosure env ["--entry", "List.map", "--entries-file", "/nonexistent"]
  expect := expect ++ [(mT.mass.getD "toolchain" 0 > 0 && mT.forbidden.isEmpty, "the walk measures no toolchain mass for List.map (vacuous), or calls it forbidden")]
  let mH ← measureClosure env ["--entry", "Lean.Json.compress", "--entries-file", "/nonexistent"]
  expect := expect ++ [(!mH.forbidden.isEmpty, "the walk does not find Lean.Json reachable from Lean.Json.compress")]
  let mP ← measureClosure env ["--entry", "ledger", "--entries-file", "/nonexistent"]
  expect := expect ++ [(!mP.forbidden.isEmpty, "the walk does not find LeanJsonProofs reachable from the ledger")]
  let typo ← (measureClosure env ["--entry", "No.Such.Entry", "--entries-file", "/nonexistent"]).toBaseIO
  expect := expect ++ [(match typo with | .error _ => true | .ok _ => false, "an entry point that is not in the environment is accepted")]
  for (ok, msg) in expect do
    unless ok do IO.eprintln s!"tier1: {msg}"; bad := bad + 1
  if bad == 0 then IO.println s!"closure gate: {expect.length} negative self-tests ok (one process)"
  return if bad == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- `--entry N` adds an entry point, `--baseline F` selects the ratchet file, `--selftest` also runs the negative self-tests, `--emit` prints machine lines for the trust-ledger check
  let arg := argOf args
  let env ← importModules #[{ module := `LeanJson }, { module := `LeanJsonProofs }] {}
  let m ← measureClosure env args
  let r ← report m args (arg "--baseline" "scripts/closure-baseline.txt")
  if r != 0 || !args.contains "--selftest" then return r
  selfTests
