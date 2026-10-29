import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Analytic bounds for the shifted Gaussian tail integral. -/
namespace BstLean.Part217
open MeasureTheory Real Set
open scoped ENNReal

noncomputable def shiftedIntegral (c b : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (exp (b * v - c * v ^ 2 / 2))

lemma shiftedIntegral_mono {c c' b b' : ℝ} (hc : c ≤ c') (hb : b' ≤ b) :
    shiftedIntegral c' b' ≤ shiftedIntegral c b := by
  apply lintegral_mono_ae
  apply (ae_restrict_iff' measurableSet_Ioi).mpr
  exact ae_of_all _ fun v hv => ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by
    have hv0 : 0 ≤ v := le_of_lt hv
    nlinarith [mul_le_mul_of_nonneg_right hb hv0,
      mul_le_mul_of_nonneg_right hc (sq_nonneg v)]))

theorem shiftedIntegral_exponential {c b : ℝ} (hc : 0 ≤ c) (hb : b < 0) :
    shiftedIntegral c b ≤ ENNReal.ofReal (1 / (-b)) := by
  have hi := integrableOn_exp_mul_Ioi hb 0
  calc shiftedIntegral c b ≤ ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (exp (b * v)) := by
        apply lintegral_mono
        intro v
        exact ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by nlinarith [sq_nonneg v]))
    _ = ENNReal.ofReal (1 / (-b)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun v => (exp_pos _).le),
          integral_exp_mul_Ioi hb]
        simp [div_eq_mul_inv]

theorem shiftedIntegral_halfGaussian {c b : ℝ} (hc : 0 < c) (hb : b ≤ 0) :
    shiftedIntegral c b ≤ ENNReal.ofReal (sqrt (π / (2 * c))) := by
  have hi : IntegrableOn (fun v : ℝ => exp (-(c / 2) * v ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq (show 0 < c / 2 by linarith)).integrableOn
  calc shiftedIntegral c b ≤ ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (exp (-(c / 2) * v ^ 2)) := by
        apply lintegral_mono_ae
        apply (ae_restrict_iff' measurableSet_Ioi).mpr
        exact ae_of_all _ fun v hv => ENNReal.ofReal_le_ofReal (exp_le_exp.mpr (by
          have : b * v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb (le_of_lt hv)
          nlinarith))
    _ = ENNReal.ofReal (sqrt (π / (2 * c))) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun v => (exp_pos _).le),
          integral_gaussian_Ioi]
        congr 1
        rw [← sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), ← sqrt_div (by positivity)]
        congr 1
        field_simp
        norm_num

theorem shiftedIntegral_negative_min {c b : ℝ} (hc : 0 < c) (hb : b < 0) :
    shiftedIntegral c b ≤ ENNReal.ofReal (min (1 / (-b)) (sqrt (π / (2 * c)))) := by
  rw [ENNReal.ofReal_min]
  exact le_min (shiftedIntegral_exponential hc.le hb) (shiftedIntegral_halfGaussian hc hb.le)

theorem shiftedIntegral_fullGaussian {c b : ℝ} (hc : 0 < c) :
    shiftedIntegral c b ≤
      ENNReal.ofReal (sqrt (2 * π / c) * exp (max b 0 ^ 2 / (2 * c))) := by
  set B := max b 0
  have hB : b ≤ B := le_max_left _ _
  have he : ∀ v : ℝ, B * v - c * v ^ 2 / 2 =
      B ^ 2 / (2 * c) + (-(c / 2) * (v + -(B / c)) ^ 2) := by
    intro v
    field_simp
    <;> ring
  have hf : Measurable (fun v : ℝ => ENNReal.ofReal (exp (-(c / 2) * v ^ 2))) := by
    fun_prop
  calc shiftedIntegral c b ≤ shiftedIntegral c B := shiftedIntegral_mono le_rfl hB
    _ ≤ ∫⁻ v : ℝ, ENNReal.ofReal (exp (B * v - c * v ^ 2 / 2)) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal (exp (B ^ 2 / (2 * c))) *
        ∫⁻ v : ℝ, ENNReal.ofReal (exp (-(c / 2) * v ^ 2)) := by
      simp_rw [he, exp_add, ENNReal.ofReal_mul (exp_pos _).le]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_add_right_eq_self
        (fun v : ℝ => ENNReal.ofReal (exp (-(c / 2) * v ^ 2))) (-(B / c))
    _ = ENNReal.ofReal (sqrt (2 * π / c) * exp (B ^ 2 / (2 * c))) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (integrable_exp_neg_mul_sq (show 0 < c / 2 by linarith))
        (ae_of_all _ fun v => (exp_pos _).le), integral_gaussian,
        ← ENNReal.ofReal_mul (exp_pos _).le]
      congr 1
      rw [mul_comm]
      congr 2
      field_simp

lemma shiftedIntegral_ne_top {c b : ℝ} (hc : 0 < c) : shiftedIntegral c b ≠ ⊤ :=
  ne_of_lt ((shiftedIntegral_fullGaussian hc).trans_lt ENNReal.ofReal_lt_top)

end BstLean.Part217
