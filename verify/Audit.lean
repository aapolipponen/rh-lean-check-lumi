/-
Audit.lean -- independent end-of-build audit.  Imports only `Lean` (never the project), so no
project macro / elaborator / notation can influence what it prints.

  LEAN_PATH=<dep oleans>:<build/lib> lean --run Audit.lean OUT_DIR ROOT [thm=ExpectedType ...]

Loads the compiled environment of ROOT without running any project initialisers and, for every
`thm=Expected` pair:
  * checks `thm` is a theorem whose statement is literally the constant `Expected`
  * walks every constant the proof depends on (types and values, transitively)
  * reports every axiom reached (only propext, Classical.choice, Quot.sound are acceptable)
  * reports which module each expected statement lives in
Writes OUT_DIR/used-modules.txt (modules that contribute at least one constant to the proofs) and
OUT_DIR/audit-result.txt.  Exit code 0 only if everything is as expected.
-/
import Lean
open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def constDeps (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.type.getUsedConstants
  match ci with
  | .defnInfo v   => out := out ++ v.value.getUsedConstants
  | .thmInfo v    => out := out ++ v.value.getUsedConstants
  | .opaqueInfo v => out := out ++ v.value.getUsedConstants
  | .inductInfo v => out := out ++ v.ctors.toArray
  | .ctorInfo v   => out := out.push v.induct
  | .recInfo v    =>
    out := out ++ v.all.toArray
    for r in v.rules do out := out ++ r.rhs.getUsedConstants
  | .quotInfo _   => pure ()
  | .axiomInfo _  => pure ()
  return out

structure Walk where
  seen    : Std.HashSet Name := {}
  axioms  : NameSet := {}
  missing : NameSet := {}
  unsafeC : NameSet := {}
  partialC : NameSet := {}

def walk (env : Environment) (root : Name) (st : Walk) : Walk := Id.run do
  let mut st := st
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if st.seen.contains n then continue
    st := { st with seen := st.seen.insert n }
    match env.find? n with
    | none => st := { st with missing := st.missing.insert n }
    | some ci =>
      if ci.isUnsafe then st := { st with unsafeC := st.unsafeC.insert n }
      if ci.isPartial then st := { st with partialC := st.partialC.insert n }
      if let .axiomInfo _ := ci then st := { st with axioms := st.axioms.insert n }
      for d in constDeps ci do
        if !st.seen.contains d then stack := stack.push d
  return st

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString env.header.moduleNames[i.toNat]!
  | none => "<none>"

unsafe def main (args : List String) : IO UInt32 := do
  let outDir :: root :: pairs := args
    | IO.eprintln "usage: Audit OUT_DIR ROOT thm=Expected ..."; return 2
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := root.toName }] {} (trustLevel := 1024) (loadExts := false)
  let t1 ← IO.monoMsNow
  let mut lines : Array String := #[]
  let mut ok := true
  lines := lines.push s!"root {root}: {env.header.moduleNames.size} modules loaded in {t1 - t0} ms"
  IO.println s!"[progress] loaded {env.header.moduleNames.size} modules in {t1 - t0} ms"
  (← IO.getStdout).flush
  let mut st : Walk := {}
  for p in pairs do
    if p == "@root" then
      -- test mode: walk every constant declared in the root module itself
      let some ri := env.header.moduleNames.findIdx? (· == root.toName) | return 2
      let mut k := 0
      for (n, _) in env.constants.map₁.toList do
        if (env.getModuleIdxFor? n).map (·.toNat) == some ri then
          st := walk env n st
          k := k + 1
      lines := lines.push s!"@root: walked {k} constants declared in {root}; axioms reached: {st.axioms.toList}"
      continue
    if p.startsWith "@each=" then
      -- per-theorem footprint: an independent walk from each listed constant (in parallel), plus whether
      -- the targets audited so far reach it.  Put this argument after the thm=Expected pairs.
      let file := (p.splitOn "=")[1]!
      let names := (← IO.FS.lines file).toList.filter (· != "") |>.map String.toName
      let mainSeen := st.seen
      let tasks := names.map fun n => Task.spawn fun _ =>
        let w := walk env n {}
        let mods : Std.HashSet Nat := w.seen.toList.foldl (init := {}) fun acc c =>
          match env.getModuleIdxFor? c with
          | some i => acc.insert i.toNat
          | none => acc
        (n, w.seen.size, mods, w.axioms.toList)
      let mut rowsOut : Array String := #["name\tfound\treached_by_main\tconstants\tmodules\taxioms\tmodules_by_library"]
      for t in tasks do
        let (n, k, mods, ax) := t.get
        let mut byRoot : Std.HashMap String Nat := {}
        for i in mods.toList do
          let r := ((toString env.header.moduleNames[i]!).splitOn ".").headD ""
          byRoot := byRoot.insert r (byRoot.getD r 0 + 1)
        let br := String.intercalate "," ((byRoot.toArray.qsort (fun x y => x.2 > y.2)).toList.map fun (r, c) => s!"{r}={c}")
        rowsOut := rowsOut.push s!"{n}\t{env.contains n}\t{mainSeen.contains n}\t{k}\t{mods.size}\t{ax}\t{br}"
      IO.FS.writeFile (System.FilePath.mk outDir / "per-theorem.tsv") (String.intercalate "\n" rowsOut.toList ++ "\n")
      lines := lines.push s!"@each: wrote footprints of {names.length} constants to per-theorem.tsv"
      continue
    let [thm, expected] := p.splitOn "="
      | IO.eprintln s!"bad pair {p}"; return 2
    let thmN := thm.toName
    let expN := expected.toName
    match env.find? thmN with
    | none =>
      ok := false
      lines := lines.push s!"FAIL {thm}: not found in environment"
    | some ci =>
      let isThm := match ci with | .thmInfo _ => true | _ => false
      let stmtOk := ci.type == .const expN [] && ci.levelParams.isEmpty
      if !isThm then ok := false
      if !stmtOk then ok := false
      lines := lines.push s!"{if isThm && stmtOk then "ok  " else "FAIL"} {thm} : {ci.type}   [theorem={isThm} statement-is-{expected}={stmtOk}] defined in {moduleOf env thmN}"
      match env.find? expN with
      | some (.defnInfo d) =>
        lines := lines.push s!"     {expected} is a def in module {moduleOf env expN}, type {d.type}"
        lines := lines.push s!"     {expected} := {d.value}"
      | _ =>
        ok := false
        lines := lines.push s!"FAIL {expected}: not a definition"
      -- one shared walk over all targets (the five theorems share almost all dependencies);
      -- axioms are reported for the union below
      st := walk env thmN st
      lines := lines.push s!"     walked {thm}: {st.seen.size} constants reached so far, axioms so far {st.axioms.toList}"
      IO.println s!"[progress] walked {thm}: {st.seen.size} constants so far at {(← IO.monoMsNow) - t0} ms"
      (← IO.getStdout).flush
  let badAx := st.axioms.toList.filter (!allowedAxioms.contains ·)
  if !badAx.isEmpty then ok := false
  lines := lines.push s!"axioms reached from all targets together: {st.axioms.toList}   {if badAx.isEmpty then "(standard only)" else s!"NON-STANDARD: {badAx}"}"
  if !st.missing.isEmpty then
    ok := false
    lines := lines.push s!"FAIL constants referenced but missing: {st.missing.toList.take 20}"
  lines := lines.push s!"constants reachable from the targets: {st.seen.size}; unsafe: {st.unsafeC.size}; partial: {st.partialC.size}"
  if !st.unsafeC.isEmpty then
    ok := false
    lines := lines.push s!"FAIL unsafe constants reachable: {st.unsafeC.toList.take 20}"
  -- which modules actually contribute
  let mut used : Std.HashMap String Nat := {}
  for n in st.seen.toList do
    let m := moduleOf env n
    used := used.insert m (used.getD m 0 + 1)
  let names := used.toArray.qsort (fun a b => a.1 < b.1)
  IO.FS.writeFile (System.FilePath.mk outDir / "used-modules.txt")
    (String.intercalate "\n" (names.toList.map fun (m, k) => s!"{m} {k}") ++ "\n")
  lines := lines.push s!"modules contributing constants: {names.size} of {env.header.moduleNames.size}"
  -- every axiom declared anywhere in the loaded environment outside the standard three, used or not
  let mut allAx : Array Name := #[]
  for (n, ci) in env.constants.map₁.toList do
    if let .axiomInfo _ := ci then
      let m := moduleOf env n
      if !allowedAxioms.contains n && !(m.startsWith "Init" || m.startsWith "Lean" || m.startsWith "Std") then
        allAx := allAx.push n
  lines := lines.push s!"axioms declared outside Lean core (used or not): {allAx.toList.take 50} (total {allAx.size})"
  lines := lines.push (if ok then "AUDIT PASS" else "AUDIT FAIL")
  let text := String.intercalate "\n" lines.toList ++ "\n"
  IO.FS.writeFile (System.FilePath.mk outDir / "audit-result.txt") text
  IO.print text
  return if ok then 0 else 1
