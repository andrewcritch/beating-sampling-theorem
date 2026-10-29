import BstLean.Part243Endpoint

/-! Part 243: the scalar charge allocation of the retained 12225 row.
These rational allowances do not prove the corresponding network-event bounds. -/
namespace BstLean.Part243
open Real BstLean.Part156

noncomputable def rowEventAllowance : ℝ := 3104381678 / 10 ^ 12
noncomputable def rowSamplingAllowance : ℝ := 1 / 10 ^ 12
noncomputable def rowFailureAllowance : ℝ := 99967461 / 10 ^ 10

theorem row_sampling : 2 * exp (-100) ≤ rowSamplingAllowance := by
  have h : exp (-(25 / 32 : ℝ)) ≤ 1 / 2 := by
    apply exp_le_taylor (b := 1) 8 <;>
      norm_num [Finset.sum_range_succ, Nat.factorial]
  have he : exp (-100) = exp (-(25 / 32 : ℝ)) ^ 128 := by
    rw [← exp_nat_mul]
    norm_num
  rw [he]
  calc
    2 * exp (-(25 / 32 : ℝ)) ^ 128 ≤ 2 * (1 / 2 : ℝ) ^ 128 := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (exp_pos _).le h 128)
        (by norm_num)
    _ ≤ rowSamplingAllowance := by norm_num [rowSamplingAllowance]

/-- Each event allowance is separate. The Schur payment is exactly one epsilon.
The hidden allowance includes the distance event. -/
theorem row_event_allocation {hidden centreEnergyDirection schur latitude bias angles : ℝ}
    (hh : hidden ≤ 1194124330168 / 10 ^ 15)
    (hc : centreEnergyDirection ≤ 495214276589 / 10 ^ 15)
    (hs : schur ≤ 1 / 4000)
    (hl : latitude ≤ 106144212354 / 10 ^ 15)
    (hb : bias ≤ 1052754646384 / 10 ^ 15)
    (ha : angles ≤ 6144212354 / 10 ^ 15) :
    hidden + (centreEnergyDirection + schur + latitude + bias + angles) ≤
      rowEventAllowance := by
  norm_num [rowEventAllowance] at *
  linarith

theorem row_complete_scalar_ledger {hidden retained : ℝ}
    (h : hidden + retained ≤ rowEventAllowance) :
    hidden + rowMoment / rowRadius ^ 2 + retained + rowSamplingAllowance +
      rowPositiveBase ^ 8 + rowNegativeBase ^ 8 ≤ rowFailureAllowance := by
  have hn : rowMoment / rowRadius ^ 2 + rowSamplingAllowance +
      rowPositiveBase ^ 8 + rowNegativeBase ^ 8 ≤
      rowFailureAllowance - rowEventAllowance := by
    norm_num [rowMoment, rowRadius, rowPositiveBase, rowNegativeBase,
      rowSamplingAllowance, rowFailureAllowance, rowEventAllowance]
  linarith

theorem row_complete_budget : rowFailureAllowance < 1 / 100 := by
  norm_num [rowFailureAllowance]

end BstLean.Part243
#print axioms BstLean.Part243.row_sampling
#print axioms BstLean.Part243.row_event_allocation
#print axioms BstLean.Part243.row_complete_scalar_ledger
#print axioms BstLean.Part243.row_complete_budget
