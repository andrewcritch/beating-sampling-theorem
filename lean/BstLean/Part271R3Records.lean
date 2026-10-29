import BstLean.Part271WorldCore

namespace BstLean.Part271.R3
/-- Outward R0 allowances; the three numbers retain their distinct meanings. -/
structure Allowances where
  hidden : ℝ
  frame : ℝ
  moment : ℝ

noncomputable def Allowances.parameters (r : Allowances) : BstLean.Part192.WorldParameters :=
  BstLean.Part271.R3.parameters r.hidden r.frame r.moment
end BstLean.Part271.R3
