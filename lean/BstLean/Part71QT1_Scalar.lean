import Mathlib

/-! Part 71, Theorem QT1, scalar and one-dimensional Gaussian pieces. -/

namespace BstLean.Part71

open MeasureTheory ProbabilityTheory

/-- `1 ≤ (1 − u) exp(u + u²)` for `u ≤ 1/2`. -/
theorem log_ineq (u : ℝ) (hu : u ≤ 1 / 2) : 1 ≤ (1 - u) * Real.exp (u + u ^ 2) := by
  rcases le_or_gt u 0 with h | h
  · have he := Real.add_one_le_exp (u + u ^ 2)
    have h1 : 0 ≤ 1 - u := by linarith
    have : (1 - u) * (u + u ^ 2 + 1) ≤ (1 - u) * Real.exp (u + u ^ 2) :=
      mul_le_mul_of_nonneg_left he h1
    nlinarith [pow_two_nonneg u, mul_nonpos_iff.mpr (Or.inr ⟨h, sq_nonneg u⟩)]
  · have hz : 0 ≤ u + u ^ 2 := by positivity
    have he := Real.quadratic_le_exp_of_nonneg hz
    have h1 : 0 ≤ 1 - u := by linarith
    have : (1 - u) * (1 + (u + u ^ 2) + (u + u ^ 2) ^ 2 / 2) ≤
        (1 - u) * Real.exp (u + u ^ 2) := mul_le_mul_of_nonneg_left he h1
    nlinarith [mul_pos h h, mul_pos (mul_pos h h) h, mul_pos (mul_pos h h) (mul_pos h h),
      mul_nonneg (mul_nonneg (mul_pos h h).le (mul_pos h h).le) h.le]

/-- `√(1/(1−u)) ≤ exp((u + u²)/2)` for `u ≤ 1/2`. -/
theorem sqrt_inv_le_exp (u : ℝ) (hu : u ≤ 1 / 2) :
    Real.sqrt (1 / (1 - u)) ≤ Real.exp ((u + u ^ 2) / 2) := by
  have hpos : 0 < 1 - u := by linarith
  have h := log_ineq u hu
  have h2 : 1 / (1 - u) ≤ Real.exp ((u + u ^ 2) / 2) ^ 2 := by
    rw [← Real.exp_nat_mul, div_le_iff₀ hpos]
    push_cast
    have : (2 : ℝ) * ((u + u ^ 2) / 2) = u + u ^ 2 := by ring
    rw [this]; linarith
  calc Real.sqrt (1 / (1 - u)) ≤ Real.sqrt (Real.exp ((u + u ^ 2) / 2) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = _ := Real.sqrt_sq (Real.exp_pos _).le

/-- The one-dimensional Gaussian moment generating function of `y²`. -/
theorem gauss1d_mgf (t : ℝ) (ht : t < 1 / 2) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (t * y ^ 2)) ∂gaussianReal 0 1 =
      ENNReal.ofReal (Real.sqrt (1 / (1 - 2 * t))) := by
  have hb : 0 < 1 / 2 - t := by linarith
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1) (by fun_prop)]
  have hpt : ∀ y : ℝ, (gaussianPDF 0 1 * fun y => ENNReal.ofReal (Real.exp (t * y ^ 2))) y =
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2 - t) * y ^ 2)) := by
    intro y
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    norm_num
    ring
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_const_mul, integral_gaussian]
    congr 1
    rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    have hpi := Real.pi_pos
    field_simp
  · exact (integrable_exp_neg_mul_sq hb).const_mul _
  · exact ae_of_all _ (fun y => by positivity)

end BstLean.Part71
