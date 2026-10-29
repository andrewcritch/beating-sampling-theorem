import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-! Weighted input averages retain one shared weight variable. -/
namespace BstLean.Part215
open MeasureTheory Real
open scoped ENNReal

/-- Compare the input orders before integration of the weight variable. -/
theorem weighted_order24_order64 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w : X → ℝ≥0∞) (f : X → ℝ)
    (hw : Measurable w) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    (∫⁻ x, w x * ENNReal.ofReal (f x) ^ 24 ∂μ) ^ (8 / 3 : ℝ) ≤
      (∫⁻ x, w x * ENNReal.ofReal (f x) ^ 64 ∂μ) *
        (∫⁻ x, w x ∂μ) ^ (5 / 3 : ℝ) := by
  have h := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
    (μ := μ.withDensity w) (p := 24) (q := 64) (by norm_num) (by norm_num)
    hf.aestronglyMeasurable
  simp only [eLpNorm'_eq_lintegral_enorm] at h
  simp only [Real.enorm_eq_ofReal (hf0 _), ENNReal.rpow_ofNat] at h
  rw [withDensity_apply _ MeasurableSet.univ] at h
  simp only [Measure.restrict_univ] at h
  rw [lintegral_withDensity_eq_lintegral_mul _ hw (hf.ennreal_ofReal.pow_const 24),
    lintegral_withDensity_eq_lintegral_mul _ hw (hf.ennreal_ofReal.pow_const 64)] at h
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 64)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h'
  simp only [← ENNReal.rpow_mul] at h'
  norm_num at h'
  exact h'

#print axioms weighted_order24_order64

/-- The weighted mixed moment uses pointwise weight moments and one input measure. -/
theorem weighted_mixed_moment {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    (ν : Measure W) (μ : Measure X) [SFinite ν] [SFinite μ]
    (w : X → ℝ≥0∞) (f : W → X → ℝ)
    (hw : Measurable w) (hf : Measurable (Function.uncurry f))
    (hf0 : ∀ a x, 0 ≤ f a x) {ε : ℝ≥0∞}
    (hm : ∀ x, (∫⁻ a, ENNReal.ofReal (f a x) ^ 64 ∂ν) ≤ ε ^ 64) :
    (∫⁻ a, (∫⁻ x, w x * ENNReal.ofReal (f a x) ^ 24 ∂μ) ^ (8 / 3 : ℝ) ∂ν) ≤
      ε ^ 64 * (∫⁻ x, w x ∂μ) ^ (8 / 3 : ℝ) := by
  have hpoint := fun a => weighted_order24_order64 μ w (f a) hw
    (hf.comp (measurable_const.prodMk measurable_id)) (hf0 a)
  refine (lintegral_mono hpoint).trans ?_
  have hI : Measurable (fun a => ∫⁻ x, w x * ENNReal.ofReal (f a x) ^ 64 ∂μ) :=
    Measurable.lintegral_prod_right' (ν := μ)
      ((hw.comp measurable_snd).mul (hf.ennreal_ofReal.pow_const 64))
  rw [lintegral_mul_const _ hI]
  · have hswap :
        (∫⁻ a, ∫⁻ x, w x * ENNReal.ofReal (f a x) ^ 64 ∂μ ∂ν) =
        ∫⁻ x, ∫⁻ a, w x * ENNReal.ofReal (f a x) ^ 64 ∂ν ∂μ :=
      lintegral_lintegral_swap
        (((hw.comp measurable_snd).mul (hf.ennreal_ofReal.pow_const 64)).aemeasurable)
    rw [hswap]
    have hb : (∫⁻ x, ∫⁻ a, w x * ENNReal.ofReal (f a x) ^ 64 ∂ν ∂μ) ≤
        (∫⁻ x, w x ∂μ) * ε ^ 64 := by
      calc
        _ = ∫⁻ x, w x * (∫⁻ a, ENNReal.ofReal (f a x) ^ 64 ∂ν) ∂μ := by
          congr 1
          funext x
          exact lintegral_const_mul _
            ((hf.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal.pow_const _)
        _ ≤ ∫⁻ x, w x * ε ^ 64 ∂μ := lintegral_mono fun x => mul_le_mul_right (hm x) _
        _ = _ := lintegral_mul_const _ hw
    refine (mul_le_mul_left hb _).trans_eq ?_
    rw [mul_comm (∫⁻ x, w x ∂μ), mul_assoc]
    congr 1
    have he := ENNReal.rpow_add_of_nonneg (x := ∫⁻ x, w x ∂μ)
      1 (5 / 3 : ℝ) (by norm_num) (by norm_num)
    norm_num at he
    exact he.symm

#print axioms weighted_mixed_moment
end BstLean.Part215
