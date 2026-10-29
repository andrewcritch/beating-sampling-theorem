import BstLean.Part293FinalAudit
import BstLean.Part289All
import BstLean.Part288Audit

/-!
# Declaration-level dependency map of Theorem 1

Walks the types and values of the two final theorems, transitively, through every
constant defined in an `BstLean` module (Mathlib never refers to `BstLean`, so the walk
does not descend into it). For each module it records how many of its constants the
proof uses, and how many Mathlib/other constants are referenced directly.

Run from the project root: `lake env lean tools/DepMap.lean`; it writes
`reports/depmap.tsv` (module, used BstLean constants) and `reports/depmap-external.tsv`.
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let roots : List Name :=
    [`BstLean.Part293.classifier_stated2_8000, `BstLean.Part289.progOut_run2]
  let modName (c : Name) : Name :=
    match env.getModuleIdxFor? c with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => `«current»
  let isOurs (c : Name) : Bool := (modName c).getRoot == `BstLean
  let mut visited : NameSet := {}
  let mut stack : Array Name := roots.toArray
  let mut perModule : Std.HashMap Name Nat := {}
  let mut external : Std.HashMap Name Nat := {}
  while !stack.isEmpty do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    let m := modName c
    if !isOurs c then
      external := external.insert m (external.getD m 0 + 1)
      continue
    perModule := perModule.insert m (perModule.getD m 0 + 1)
    match env.find? c with
    | none => pure ()
    | some info =>
      let deps := info.type.getUsedConstants ++
        (match info.value? (allowOpaque := true) with
         | some v => v.getUsedConstants
         | none => #[])
      for d in deps do
        unless visited.contains d do stack := stack.push d
  let ours := perModule.toList.map (fun (m, k) => s!"{m}\t{k}")
  let ext := external.toList.map (fun (m, k) => s!"{m}\t{k}")
  IO.FS.writeFile "reports/depmap.tsv" (String.intercalate "\n" ours ++ "\n")
  IO.FS.writeFile "reports/depmap-external.tsv" (String.intercalate "\n" ext ++ "\n")
  IO.println s!"BstLean modules used: {perModule.size}; constants visited: {visited.size}"
