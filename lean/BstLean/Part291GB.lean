import BstLean.Part215Mixed
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! The two Holder steps of GB. The exponents require energy order 32 and
gradient order 24; no higher gradient moment is used. -/
namespace BstLean.BlueprintLow
open MeasureTheory
open scoped ENNReal

/-- Weighted interpolation keeps the same V in both Holder factors. -/
theorem gb_interpolation {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (V Z : X → ℝ≥0∞) (hV : Measurable V) (hZ : Measurable Z) :
    (∫⁻ x, V x * Z x ∂μ) ≤
      (∫⁻ x, V x ∂μ) ^ (41 / 45 : ℝ) *
        (∫⁻ x, V x * Z x ^ (45 / 4 : ℝ) ∂μ) ^ (4 / 45 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (45 / 41 : ℝ).HolderConjugate (45 / 4) by
      norm_num [Real.holderConjugate_iff])
    (hV.pow_const (41 / 45 : ℝ)).aemeasurable
    ((hV.pow_const (4 / 45 : ℝ)).mul hZ).aemeasurable
  have hp : (fun x => V x ^ (41 / 45 : ℝ) * (V x ^ (4 / 45 : ℝ) * Z x)) =
      fun x => V x * Z x := by
    funext x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  simp only [Pi.mul_apply] at h
  rw [hp] at h
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 45 / 4),
    ← ENNReal.rpow_mul] at h
  norm_num at h
  exact h

/-- The second Holder step uses 16 * (45/4) / 15 = 12. Here g is the
squared gradient, so its twelfth moment is gradient order 24. -/
theorem gb_energy_gradient {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ω g : X → ℝ≥0∞) (hω : Measurable ω) (hg : Measurable g) :
    (∫⁻ x, ω x * g x ^ (45 / 4 : ℝ) ∂μ) ≤
      (∫⁻ x, ω x ^ 16 ∂μ) ^ (1 / 16 : ℝ) *
        (∫⁻ x, g x ^ 12 ∂μ) ^ (15 / 16 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (show (16 : ℝ).HolderConjugate (16 / 15) by norm_num [Real.holderConjugate_iff])
    hω.aemeasurable (hg.pow_const (45 / 4 : ℝ)).aemeasurable
  simp only [← ENNReal.rpow_mul] at h
  norm_num at h
  exact h

/-- GB before inserting the concrete network moments. V may depend on both
the energy and gradient. The pointwise envelope is not an independence premise. -/
theorem gb_moment_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (V Z ω g : X → ℝ≥0∞)
    (hV : Measurable V) (hZ : Measurable Z) (hω : Measurable ω) (hg : Measurable g)
    {K F L E G : ℝ≥0∞}
    (hVω : ∀ x, V x ≤ K * ω x) (hZg : ∀ x, Z x ≤ F * g x)
    (hL : (∫⁻ x, V x ∂μ) ≤ L)
    (hE : (∫⁻ x, ω x ^ 16 ∂μ) ≤ E) (hG : (∫⁻ x, g x ^ 12 ∂μ) ≤ G) :
    (∫⁻ x, V x * Z x ∂μ) ≤
      L ^ (41 / 45 : ℝ) *
        (K * F ^ (45 / 4 : ℝ) *
          (E ^ (1 / 16 : ℝ) * G ^ (15 / 16 : ℝ))) ^ (4 / 45 : ℝ) := by
  have hm : (∫⁻ x, V x * Z x ^ (45 / 4 : ℝ) ∂μ) ≤
      K * F ^ (45 / 4 : ℝ) *
        (E ^ (1 / 16 : ℝ) * G ^ (15 / 16 : ℝ)) := by
    calc
      _ ≤ ∫⁻ x, (K * ω x) * (F * g x) ^ (45 / 4 : ℝ) ∂μ := by
        apply lintegral_mono
        intro x
        exact mul_le_mul' (hVω x) (ENNReal.rpow_le_rpow (hZg x) (by norm_num))
      _ = K * F ^ (45 / 4 : ℝ) * (∫⁻ x, ω x * g x ^ (45 / 4 : ℝ) ∂μ) := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 45 / 4)]
        have he : (fun x => (K * ω x) * (F ^ (45 / 4 : ℝ) * g x ^ (45 / 4 : ℝ))) =
            fun x => (K * F ^ (45 / 4 : ℝ)) * (ω x * g x ^ (45 / 4 : ℝ)) := by
          funext x; ring
        rw [he]
        exact lintegral_const_mul _ (show Measurable (fun x => ω x * g x ^ (45 / 4 : ℝ)) from hω.mul (hg.pow_const _))
      _ ≤ _ := mul_le_mul' le_rfl ((gb_energy_gradient μ ω g hω hg).trans
        (mul_le_mul' (ENNReal.rpow_le_rpow hE (by norm_num))
          (ENNReal.rpow_le_rpow hG (by norm_num))))
  exact (gb_interpolation μ V Z hV hZ).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow hL (by norm_num))
      (ENNReal.rpow_le_rpow hm (by norm_num)))

end BstLean.BlueprintLow
