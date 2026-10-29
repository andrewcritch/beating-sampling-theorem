import BstLean.Part291RWRows
import BstLean.Part291CoreRows

/-! The capped density preserves the original measure. Its domination bounds
are used only for exceptional, shell, and outside terms. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open BstLean.Part188

theorem weight_mean_from_RW {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    {a d m s : ℝ} (hd : 0 < d) (hY : d < a - m ^ 2)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (h : RWDeficitMoments μ f m s) :
    (∫ x, weight a d (f x) ∂μ) ≤ √(rwWeightMean a d m s) := by
  have hmean := (rwWeightMoments μ f hf hd hY hm hs h).2.1
  have hsq := BstLean.Part162.mean_sq_le (μ := μ) (measurable_weight a d hf)
    (fun x => by
      rw [abs_of_nonneg (show 0 ≤ weight a d (f x) from sqrt_nonneg _)]
      exact sqrt_le_sqrt (weightSq_le_inv hd))
  simp_rw [weight, sq_sqrt (weightSq_nonneg hd)] at hsq
  exact le_sqrt_of_sq_le (hsq.trans hmean)

theorem weighted_density_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w f : X → ℝ) (hw : Measurable w) (hf : Measurable f)
    {a d : ℝ} (hd : 0 < d) (hw0 : ∀ x, 0 ≤ w x)
    (hi : Integrable w μ) (hi2 : Integrable (fun x => w x ^ 2) μ) :
    Integrable (fun x => w x * weightSq a d (f x)) μ ∧
    Integrable (fun x => (w x * weightSq a d (f x)) ^ 2) μ := by
  have hq : Measurable (fun x => weightSq a d (f x)) := by unfold weightSq; fun_prop
  constructor
  · apply (hi.mul_const (1 / d)).mono' (hw.mul hq).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (weightSq_nonneg hd))]
      exact mul_le_mul_of_nonneg_left (weightSq_le_inv hd) (hw0 x)
  · apply (hi2.mul_const ((1 / d) ^ 2)).mono' ((hw.mul hq).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (weightSq_nonneg hd) (weightSq_le_inv hd) 2) (sq_nonneg _)

theorem weighted_integral_domination {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    {a d : ℝ} (hd : 0 < d) (hg0 : ∀ x, 0 ≤ g x) (hi : Integrable g μ) :
    Integrable (fun x => weightSq a d (f x) * g x) μ ∧
    (∫ x, weightSq a d (f x) * g x ∂μ) ≤ (∫ x, g x ∂μ) / d := by
  have hq : Measurable (fun x => weightSq a d (f x)) := by unfold weightSq; fun_prop
  have hiq : Integrable (fun x => weightSq a d (f x) * g x) μ := by
    apply (hi.const_mul (1 / d)).mono' (hq.mul hg).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weightSq_nonneg hd) (hg0 x))]
      exact mul_le_mul_of_nonneg_right (weightSq_le_inv hd) (hg0 x)
  refine ⟨hiq, ?_⟩
  have h := integral_mono hiq (hi.const_mul (1 / d))
    (fun x => mul_le_mul_of_nonneg_right (weightSq_le_inv hd) (hg0 x))
  rw [integral_const_mul] at h
  exact h.trans_eq (by ring)

theorem weighted_fourth_domination {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    {a d : ℝ} (hd : 0 < d) (hg0 : ∀ x, 0 ≤ g x) (hi : Integrable g μ) :
    Integrable (fun x => weightSq a d (f x) ^ 2 * g x) μ ∧
    (∫ x, weightSq a d (f x) ^ 2 * g x ∂μ) ≤ (∫ x, g x ∂μ) / d ^ 2 := by
  have hq : Measurable (fun x => weightSq a d (f x) ^ 2) := by unfold weightSq; fun_prop
  have hb x : weightSq a d (f x) ^ 2 ≤ 1 / d ^ 2 := by
    simpa only [div_pow, one_pow] using
      pow_le_pow_left₀ (weightSq_nonneg hd) (weightSq_le_inv hd) 2
  have hiq : Integrable (fun x => weightSq a d (f x) ^ 2 * g x) μ := by
    apply (hi.const_mul (1 / d ^ 2)).mono' (hq.mul hg).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 x))]
      exact mul_le_mul_of_nonneg_right (hb x) (hg0 x)
  refine ⟨hiq, ?_⟩
  have h := integral_mono hiq (hi.const_mul (1 / d ^ 2))
    (fun x => mul_le_mul_of_nonneg_right (hb x) (hg0 x))
  rw [integral_const_mul] at h
  exact h.trans_eq (by ring)

end BstLean.BlueprintLow
