import BstLean.Part249Ledger

/-! Failure of a sufficient scalar substitution, not a lower bound on network error.
The stored row uses local covariance and centre bounds. Replacing those by the
available uniform covariance certificate and a global centre allowance loses the row. -/
namespace BstLean.Part249

noncomputable def storedFrameCutoff : ℝ := 246209841 / 10 ^ 9
noncomputable def globalCentreAllowance : ℝ := 93590842309101 / 10 ^ 15
noncomputable def storedMassAllowance : ℝ := 11 / 1000

theorem stored_frame_cutoff_ge : (1 / 5 : ℝ) ≤ storedFrameCutoff := by
  norm_num [storedFrameCutoff]

theorem uniform_covariance_frame_fails :
    optionBAgentFrame <
      (BstLean.Part246.ratCov (67 / 100) (60 / 100) (13 / 10) +
        globalCentreAllowance) / storedFrameCutoff + storedMassAllowance := by
  norm_num [optionBAgentFrame, BstLean.Part246.ratCov, globalCentreAllowance,
    storedFrameCutoff, storedMassAllowance]

/-- Charging the moment event in addition to all old allowances loses the budget.
The revised bridge instead requires a base-event bound after removal of this payment. -/
theorem extra_moment_payment_fails :
    (1 / 100 : ℝ) < optionBLedger + 5 / 100000 := by
  have := optionB_ledger_bounds.1
  linarith

end BstLean.Part249
