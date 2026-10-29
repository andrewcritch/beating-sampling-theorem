import BstLean.Part209Kernel

/-! An analytic proof of the projected kernel derivative bound. -/
namespace BstLean.Part209
open Real Set
open BstLean.Part130 BstLean.Part132

lemma arcsin_mul_sqrt_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    arcsin r * sqrt (1 - r ^ 2) ≤ r := by
  rcases eq_or_lt_of_le hr0 with hr | hr
  · rw [← hr]
    simp
  rcases eq_or_lt_of_le hr1 with hr1 | hr1
  · rw [hr1]
    simp
  have hs : 0 < sqrt (1 - r ^ 2) := sqrt_pos.mpr (by nlinarith)
  have h := arcsin_convexOn.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ⟨hr.le, hr1.le⟩ hr
    (Real.hasDerivAt_arcsin (by linarith : r ≠ -1) hr1.ne)
  rw [slope_def_field, arcsin_zero, sub_zero, sub_zero, div_le_iff₀ hr] at h
  have h' := mul_le_mul_of_nonneg_right h hs.le
  calc arcsin r * sqrt (1 - r ^ 2) ≤ (sqrt (1 - r ^ 2))⁻¹ * r * sqrt (1 - r ^ 2) := by
        simpa only [one_div] using h'
    _ = r := by field_simp

/-- The paper constant `0.6` follows from elementary analytic inequalities. -/
theorem projected_kernelSlope_le {r : ℝ} (hr0 : -1 ≤ r) (hr1 : r ≤ 1) :
    kernelSlope r * sqrt (1 - r ^ 2) ≤ 3 / 5 := by
  have hs0 : 0 ≤ sqrt (1 - r ^ 2) := sqrt_nonneg _
  have hs2 : sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 := sq_sqrt (by nlinarith)
  have hs1 : sqrt (1 - r ^ 2) ≤ 1 := by nlinarith [sq_nonneg r]
  have he : kernelSlope r = 1 / 2 + arcsin r / π := kappa_deriv_eq r
  rcases le_total r 0 with hr | hr
  · have ha : arcsin r ≤ 0 := Real.arcsin_nonpos.mpr hr
    have hk : kernelSlope r ≤ 1 / 2 := by rw [he]; exact add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg ha pi_pos.le)
    have h := mul_le_mul_of_nonneg_right hk hs0
    nlinarith
  · have ha := arcsin_mul_sqrt_le hr hr1
    have hdiv := div_le_div_of_nonneg_right ha pi_pos.le
    have hpi : 1 / π ≤ 8 / 25 := by
      rw [div_le_iff₀ pi_pos]
      nlinarith [Real.pi_gt_d4]
    have hlinear : kernelSlope r * sqrt (1 - r ^ 2) ≤
        sqrt (1 - r ^ 2) / 2 + 8 / 25 * r := by
      rw [he]
      have h := mul_le_mul_of_nonneg_right hpi hr
      simp only [div_eq_mul_inv] at hdiv h ⊢
      nlinarith
    have hsq := sq_nonneg (8 / 25 * sqrt (1 - r ^ 2) - r / 2)
    have htarget : sqrt (1 - r ^ 2) / 2 + 8 / 25 * r ≤ (3 : ℝ) / 5 := by
      nlinarith [sq_nonneg (sqrt (1 - r ^ 2) / 2 + 8 / 25 * r - 3 / 5)]
    exact hlinear.trans htarget

end BstLean.Part209
