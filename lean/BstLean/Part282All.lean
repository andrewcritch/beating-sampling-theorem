import BstLean.Part282NodeFull
import BstLean.Part282Out
import BstLean.Part282Count
import BstLean.Part282Agent

/-!
# Part 282 (C2): index

* `Part282Kit`: combinators (`RExpr`, `RProg.ext`, `parL`, `iter`, `horner`, indicators).
* `Part282Draw`: one draw (`latProg`, `selectNode`, `hitProg`, `hitFn_eq_hitProg`).
* `Part282Row`: one even sphere row (`rowProg`, `a1St_eq_rowProg`, `e1St_eq_rowProg`).
* `Part282Node`, `Part282NodeFull`: one node pass (`nodeProg`, `passFSt_eq_nodeProg`,
  `passWSt_eq_nodeProg`).
* `Part282Out`: the output rule (`outProg`, `progOut_eq_outProg`).
* `Part282Agent`: the global Agent pass (`agentProg`, `bAp_eq_agentProg`, for `τ₀ > 0`).
* `Part282Count`: the corrected schedule `orderedWork''` and `paperCount''_lt`.
-/

/-- info: 'BstLean.Part282.latProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.latProg_eval
/-- info: 'BstLean.Part282.selectNode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.selectNode_eq
/-- info: 'BstLean.Part282.selectNode_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.selectNode_count
/-- info: 'BstLean.Part282.hitFn_eq_hitProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.hitFn_eq_hitProg
/-- info: 'BstLean.Part282.hitProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.hitProg_cost
/-- info: 'BstLean.Part282.rowProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rowProg_eval
/-- info: 'BstLean.Part282.rowProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rowProg_cost
/-- info: 'BstLean.Part282.passFSt_eq_nodeProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.passFSt_eq_nodeProg
/-- info: 'BstLean.Part282.passWSt_eq_nodeProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.passWSt_eq_nodeProg
/-- info: 'BstLean.Part282.nodeProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.nodeProg_cost
/-- info: 'BstLean.Part282.progOut_eq_outProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.progOut_eq_outProg
/-- info: 'BstLean.Part282.outProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.outProg_cost
/-- info: 'BstLean.Part282.paperCount''_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.paperCount''_lt
/-- info: 'BstLean.Part282.bAp_eq_agentProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.bAp_eq_agentProg
