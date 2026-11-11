import Lean
import LeanJsonProofs.Ledger
import LeanJson
/-! Ledger gate (adapted from the ledger gate of the project these gates were first built in): renders `docs/proof-ledger.md` from
`LeanJsonProofs/Ledger.lean`, checks that every named theorem exists and is a theorem, and ratchets the counts against `scripts/ledger-baseline.txt`
(proved may only rise, open may only fall). `--write` updates the baseline. Exit 1 on regression.

"Proved" means proved about code the exports run. The gate walks the definitions the entry points (`scripts/closure-entries.txt`) reach, the same walk as
`scripts/ClosureGate.lean`, and classes every cited theorem by the `LeanJson` functions its statement mentions: yes (every one is reached), partly
(some), no (none: the statement is about a model the exports never run). A claim whose cited theorems are all `no` is shown as partial, not proved.
A definition the exports do not name but run through a refinement theorem (`scripts/ledger-bridges.txt`: `spec-def theorem reached-def`: the reference
recogniser and the fast parser) counts as reached; the theorem must exist and mention both names. With NO entry points (the skeleton) reach is not
applied: the column reads `-` and nothing is demoted; it applies from the first export on. Sorts (types, predicates) are ignored: only functions run. -/
open Lean

def isSpec (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with | some i => (env.header.moduleNames[i.toNat]!).getRoot == `LeanJson | none => false

-- the walk and the aux filter are ClosureGate's
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
        (if (env.find? (Name.str n "_unsafe_rec")).isSome then [Name.str n "_unsafe_rec"] else [])
      walk env (used.toList ++ impl ++ rest) seen

/-- A spec definition that is a function (a type or a predicate cannot be run). -/
def isFn (env : Environment) (n : Name) : Bool :=
  isSpec env n && !isAux env n && match env.find? n with
    | some ci => (let rec go : Expr → Bool | .forallE _ _ b _ => go b | .sort _ => false | _ => true; go ci.type)
    | none => false

/-- 2 = yes (every function the statement mentions is reached), 1 = partly, 0 = no (none is, or it mentions none). -/
def reachOf (env : Environment) (isReached : Name → Bool) (t : Name) : Nat :=
  let fs := ((env.find? t).map (·.type.getUsedConstants)).getD #[] |>.filter (isFn env)
  if fs.any isReached then (if fs.all isReached then 2 else 1) else 0

/-- What the ledger adds to a claim the theorems do not say by themselves (it is generated, so the wording lives here). None yet. -/
def caveats : List (String × String) := []

def readLines (p : String) : IO (List String) := do
  if !(← System.FilePath.pathExists p) then return []
  return (← IO.FS.readFile p).splitOn "\n" |>.map String.trimAscii |>.map (·.toString) |>.filter (fun l => l != "" && !l.startsWith "#")

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `LeanJsonProofs.Ledger }, { module := `LeanJson }] {}
  let arg (k : String) (d : String) : String := match args.dropWhile (· != k) with | _ :: v :: _ => v | _ => d
  let entries := (← readLines (arg "--entries-file" "scripts/closure-entries.txt")).map String.toName
  let mut bad := 0
  for e in entries do
    if (env.find? e).isNone then IO.eprintln s!"ledger: entry point {e} is not in the environment"; bad := bad + 1
  let applyReach := !entries.isEmpty
  let reach := walk env entries {}
  let nReach := reach.toList.filter (fun n => isSpec env n && !isAux env n && (match env.find? n with | some (.defnInfo _) | some (.opaqueInfo _) => true | _ => false)) |>.length
  IO.println s!"ledger: reach: {nReach} spec definitions reachable from the entry points ({entries.length} entry points)"
  let mut bridged : NameSet := {}
  for l in ← readLines (arg "--bridges" "scripts/ledger-bridges.txt") do
    match (l.splitOn " ").map String.toName with
    | [a, thm, b] =>
      let ok := reach.contains b && match env.find? thm with
        | some (.thmInfo ci) => ci.type.getUsedConstants.contains a && ci.type.getUsedConstants.contains b | _ => false
      if ok then bridged := bridged.insert a else IO.eprintln s!"ledger: bridge {a} is not backed: {thm} must be a theorem mentioning {a} and {b}, and {b} must be reached"; bad := bad + 1
    | _ => pure ()
  let isReached (n : Name) := reach.contains n || bridged.contains n
  let mut proved := 0; let mut part := 0; let mut openN := 0; let mut lim := 0; let mut demoted := 0
  let mut seenThm : NameSet := {}; let mut yesThm := 0; let mut partlyThm := 0; let mut noThm := 0; let mut provedYes := 0
  let mut rows : Array String := #[]
  for o in ledger do
    let names := match o.status with | .proved l => l | .partly l _ => l | _ => []
    for n in names do
      match env.find? n with
      | some (.thmInfo _) => pure ()
      | _ => IO.eprintln s!"ledger: {o.slug} names {n}, which is not a theorem"; bad := bad + 1
    let cls := names.map (reachOf env isReached)
    let k := cls.filter (· == 2) |>.length
    for (n, c) in names.zip cls do
      unless seenThm.contains n do
        seenThm := seenThm.insert n
        if c == 2 then yesThm := yesThm + 1 else if c == 1 then partlyThm := partlyThm + 1 else noThm := noThm + 1
    let reached := if names.isEmpty || !applyReach then "-" else if cls.all (· == 2) then "yes" else if cls.all (· == 0) then "no" else s!"partly ({k} of {names.length})"
    let tag (n : Name) : String := if !applyReach then "" else match reachOf env isReached n with | 2 => "" | 1 => " ‡" | _ => " †"
    let thmList (l : List Name) : String := ", ".intercalate (l.map fun n => s!"`{n}`{tag n}")
    let cav := match caveats.lookup o.slug with | some c => s!"; caveat: {c}" | none => ""
    match o.status with
    | .proved l =>
      if applyReach && cls.all (· == 0) && !l.isEmpty then
        demoted := demoted + 1; part := part + 1
        rows := rows.push s!"| `{o.slug}` | partial | {reached} | {thmList l}; open: not reached by the exports: every cited theorem is about a model they never run (demoted from proved by the reach rule){cav} |"
      else
        proved := proved + 1; if k == l.length then provedYes := provedYes + 1
        rows := rows.push s!"| `{o.slug}` | **proved** | {reached} | {thmList l}{cav} |"
    | .partly l n => part := part + 1; rows := rows.push s!"| `{o.slug}` | partial | {reached} | {thmList l}; open: {n}{cav} |"
    | .open_ n => openN := openN + 1; rows := rows.push s!"| `{o.slug}` | open | - | {n} |"
    | .limit n => lim := lim + 1; rows := rows.push s!"| `{o.slug}` | limit | - | {n} |"
  let total := ledger.length
  let md := "# Obligation ledger\n\nGenerated by `scripts/LedgerGate.lean` from `LeanJsonProofs/Ledger.lean`; do not edit.\n" ++
    s!"\n**{proved} proved, {part} partial, {openN} open, {lim} limit, of {total}.** Only `proved` may be called verified, and `proved` means proved about code the exports run" ++
    (if applyReach then s!": a claim whose cited theorems are all about models the exports never run is partial ({demoted} demoted by this rule)" else " (the reach rule applies from the first export: there are no entry points yet)") ++
    ". A `limit` is a claim no machine decides.\n\n" ++
    (if applyReach then s!"**reached by the exports:** {yesThm} of {seenThm.size} cited theorems are about functions the exports reach (yes), {partlyThm} about some of them (partly ‡), {noThm} about none (no †); {provedYes} of {proved} proved claims are reached through every cited theorem.\n\n" else "") ++
    "| claim (slug) | status | reached by the exports | theorems († model-only, ‡ partly), and what is still open |\n|---|---|---|---|\n" ++ "\n".intercalate rows.toList ++ "\n"
  if !(args.contains "--baseline") && bad == 0 then IO.FS.writeFile "docs/proof-ledger.md" md
  IO.println s!"ledger: {proved} proved, {part} partial, {openN} open, {lim} limit, of {total}"
  IO.println s!"ledger: reached by the exports: {yesThm} yes, {partlyThm} partly, {noThm} no of {seenThm.size} cited theorems; {provedYes} of {proved} proved claims fully reached; {demoted} demoted"
  let baseFile := arg "--baseline" "scripts/ledger-baseline.txt"
  let baseTxt ← (do if ← System.FilePath.pathExists baseFile then IO.FS.readFile baseFile else pure "")
  let baseL := baseTxt.splitOn "\n"
  if args.contains "--write" then
    -- comment lines (the documented re-bases) are kept
    let notes := baseL.filter (·.startsWith "#")
    IO.FS.writeFile baseFile (("\n".intercalate notes) ++ (if notes.isEmpty then "" else "\n") ++ s!"proved {proved}\nopen {openN}\ntotal {total}\n")
    return 0
  -- the verdict on a baseline's lines: how many ratchets it breaks
  let verdict (baseL : List String) : IO Nat := do
    let get (k : String) : Nat := (baseL.filterMap fun l => match l.splitOn " " with | [a, b] => if a == k then b.toNat? else none | _ => none).headD 0
    let mut bad := 0
    if proved < get "proved" then IO.eprintln s!"ledger: proved fell from {get "proved"} to {proved}"; bad := bad + 1
    -- open may rise only by the claims newly written down (a discovered obligation is honest; an old one silently reopened is not)
    if baseL.length > 1 && openN > get "open" + (total - get "total") then IO.eprintln s!"ledger: open rose from {get "open"} to {openN} with {total - get "total"} new claim(s)"; bad := bad + 1
    return bad
  bad := bad + (← verdict baseL)
  -- `--selftest`: the gate can fail: a baseline claiming more proved than exist must be rejected, and a baseline that has `open` rising with no new claim,
  -- in this same process
  if args.contains "--selftest" && bad == 0 then
    if (← IO.FS.withIsolatedStreams (verdict ["proved 9999", "open 0"])).2 == 0 then IO.eprintln "tier1: the ledger gate cannot fail (proved)"; return 1
    if openN > 0 && (← IO.FS.withIsolatedStreams (verdict ["proved 0", s!"open {openN - 1}", s!"total {total}"])).2 == 0 then IO.eprintln "tier1: the ledger gate cannot fail (open)"; return 1
  return if bad == 0 then 0 else 1
