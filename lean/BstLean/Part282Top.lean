import BstLean.Part282Link
import BstLean.Part282Grid
import BstLean.Part282RowData
import BstLean.Part282World

/-!
# Part 282 (C2): top file

`Part282Link` (all programs against the corrected schedule), `Part282Grid` (grid scalars and
nodes), `Part282RowData` (the row data `α_i`, `κ_i`).
-/

/-- info: 'BstLean.Part282.gridProg_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.gridProg_s
/-- info: 'BstLean.Part282.gridProg_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.gridProg_w
/-- info: 'BstLean.Part282.gridProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.gridProg_cost
/-- info: 'BstLean.Part282.rdProg_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rdProg_alpha
/-- info: 'BstLean.Part282.rdProg_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rdProg_kappa
/-- info: 'BstLean.Part282.rdProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rdProg_cost
