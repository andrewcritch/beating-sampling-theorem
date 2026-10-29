import BstLean.Part293FinalAudit
import BstLean.Part289All
import BstLean.Part288Audit

/-!
# The Beating Sampling Theorem, from "Beating Sampling: Mechanistic Estimation of the
Failure Rate of a Neural Network at Frontier Scale"

This file is the root of the extracted project. It imports only the three modules that
state the final results; their import closure is the whole project (`closure.txt`).

* `BstLean.Part293.classifier_stated2_8000`: for every `n ≥ 8000` and every real `t`, the
  program `progOut (statedDesign2 n)` succeeds, `p ≤ U ≤ max (10 p) (1/100)`, with
  probability at least `99/100` over the three random networks and the program's draws.
* `BstLean.Part289.progOut_run2`: for every `n ≥ 8000` and every input, a fully counted
  program returns `progOut (statedDesign2 n)` and uses fewer than `1.0003 · 2 n⁷`
  operations.
-/

/-- info: 'BstLean.Part293.classifier_stated2_8000' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000

/-- info: 'BstLean.Part289.progOut_run2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.progOut_run2
