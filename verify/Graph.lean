/-
Graph.lean -- export the constant-level dependency graph of given theorems from the compiled tree.
Imports only `Lean`.

  LEAN_PATH=... lean --run Graph.lean OUT_DIR ROOT const1 const2 ...

Writes, streaming (so a partial run is still usable):
  OUT_DIR/graph-modules.tsv   module_index <TAB> module_name
  OUT_DIR/graph-nodes.tsv     id <TAB> kind <TAB> module_index <TAB> name     (in order of first visit)
  OUT_DIR/graph-edges.txt     id <TAB> ids used by the type (space separated) <TAB> ids used by the value/body
  OUT_DIR/graph-progress.txt  progress lines
kind: thm def opaque induct ctor rec quot axiom missing.  module_index -1: no module.
For inductives the "value" column lists constructors; for constructors the inductive; for recursors
the mutual inductives and the constants of the recursor rules.
-/
import Lean
open Lean

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot" | .axiomInfo _ => "axiom"

def bodyDeps (ci : ConstantInfo) : Array Name := Id.run do
  match ci with
  | .defnInfo v   => v.value.getUsedConstants
  | .thmInfo v    => v.value.getUsedConstants
  | .opaqueInfo v => v.value.getUsedConstants
  | .inductInfo v => v.ctors.toArray
  | .ctorInfo v   => #[v.induct]
  | .recInfo v    =>
    let mut out := v.all.toArray
    for r in v.rules do out := out ++ r.rhs.getUsedConstants
    out
  | _ => #[]

unsafe def main (args : List String) : IO UInt32 := do
  let outDir :: root :: targets := args
    | IO.eprintln "usage: Graph OUT_DIR ROOT const ..."; return 2
  let dir := System.FilePath.mk outDir
  let prog ← IO.FS.Handle.mk (dir / "graph-progress.txt") .write
  let say (s : String) : IO Unit := do prog.putStrLn s; prog.flush
  initSearchPath (← findSysroot)
  let t0 ← IO.monoMsNow
  let env ← importModules #[{ module := root.toName }] {} (trustLevel := 1024) (loadExts := false)
  say s!"loaded {env.header.moduleNames.size} modules in {(← IO.monoMsNow) - t0} ms"
  let hm ← IO.FS.Handle.mk (dir / "graph-modules.tsv") .write
  let mut i := 0
  for m in env.header.moduleNames do
    hm.putStrLn s!"{i}\t{m}"
    i := i + 1
  hm.flush
  let hn ← IO.FS.Handle.mk (dir / "graph-nodes.tsv") .write
  let he ← IO.FS.Handle.mk (dir / "graph-edges.txt") .write
  let mut ids : Std.HashMap Name Nat := {}
  let mut stack : Array Name := #[]
  for t in targets do
    let n := t.toName
    if !ids.contains n then
      ids := ids.insert n ids.size
      stack := stack.push n
  let mut done := 0
  let mut axioms : Array Name := #[]
  let mut missing := 0
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    let id := ids[n]!
    match env.find? n with
    | none =>
      missing := missing + 1
      hn.putStrLn s!"{id}\tmissing\t-1\t{n}"
    | some ci =>
      let mi : Int := match env.getModuleIdxFor? n with | some i => i.toNat | none => -1
      hn.putStrLn s!"{id}\t{kindOf ci}\t{mi}\t{n}"
      if let .axiomInfo _ := ci then axioms := axioms.push n
      let mut line := s!"{id}\t"
      let mut first := true
      for d in ci.type.getUsedConstants do
        if !ids.contains d then
          ids := ids.insert d ids.size
          stack := stack.push d
        line := line ++ (if first then "" else " ") ++ toString ids[d]!
        first := false
      line := line ++ "\t"
      first := true
      for d in bodyDeps ci do
        if !ids.contains d then
          ids := ids.insert d ids.size
          stack := stack.push d
        line := line ++ (if first then "" else " ") ++ toString ids[d]!
        first := false
      he.putStrLn line
    done := done + 1
    if done % 50000 == 0 then
      hn.flush; he.flush
      say s!"{done} constants written, {stack.size} on stack, {ids.size} seen, at {(← IO.monoMsNow) - t0} ms"
  hn.flush; he.flush
  say s!"DONE {done} constants, missing {missing}, axioms {axioms.toList}, at {(← IO.monoMsNow) - t0} ms"
  IO.println s!"graph: {done} constants, missing {missing}, axioms {axioms.toList}"
  (← IO.getStdout).flush
  IO.Process.exit 0
