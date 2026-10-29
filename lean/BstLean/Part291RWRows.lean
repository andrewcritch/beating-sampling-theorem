import BstLean.Part291RWWeight
import BstLean.Part208CoreRow

/-! RW rows with a dependent reciprocal density. The unweighted row is the
only input to which the original axial symmetry can be applied. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part188

theorem rw_row_of_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f w g : X → ℝ)
    (hf : Measurable f) (hw : Measurable w) (hg : Measurable g)
    {a d m s K G A R : ℝ} (hd : 0 < d) (hY : d < a - m ^ 2)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hfK : ∀ x, |f x| ≤ K) (hw0 : ∀ x, 0 ≤ w x)
    (hg0 : ∀ x, 0 ≤ g x) (hgG : ∀ x, g x ≤ G)
    (hiw : Integrable w μ) (hiw2 : Integrable (fun x => w x ^ 2) μ)
    (hrow : (∫ x, w x * g x ∂μ) ≤ A)
    (hw2 : (∫ x, w x ^ 2 ∂μ) ≤ R ^ 2)
    (hD : RWDeficitMoments μ f m s) :
    (∫ x, weightSq a d (f x) * (w x * g x) ∂μ) ≤
      A / (a - m ^ 2) + rwDelta a d m s * (G * R) := by
  let e := fun x => reciprocalExcess a d m (f x)
  let E := K ^ 2 / (a - m ^ 2) ^ 2 + K ^ 4 / (d * (a - m ^ 2) ^ 2)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he0 : ∀ x, 0 ≤ e x := fun _ => reciprocalExcess_nonneg hd
  have hem : Measurable e := by unfold e reciprocalExcess; fun_prop
  have heE : ∀ x, e x ≤ E := by
    intro x
    have hf2 : f x ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hfK x) 2
    have hD2 : max (f x ^ 2 - m ^ 2) 0 ≤ K ^ 2 :=
      max_le (by nlinarith [sq_nonneg m]) (sq_nonneg K)
    have hD4 : max (f x ^ 2 - m ^ 2) 0 ^ 2 ≤ K ^ 4 := by
      have h := pow_le_pow_left₀ (le_max_right _ _) hD2 2
      simpa only [← pow_mul] using h
    exact add_le_add (div_le_div_of_nonneg_right hD2 (sq_nonneg _))
      (div_le_div_of_nonneg_right hD4 (by positivity))
  have hq : Measurable (fun x => weightSq a d (f x)) := by unfold weightSq; fun_prop
  have hig : Integrable (fun x => w x * g x) μ := by
    apply (hiw.mul_const G).mono' (hw.mul hg).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 x) (hg0 x))]
      exact mul_le_mul_of_nonneg_left (hgG x) (hw0 x)
  have hiqg : Integrable (fun x => weightSq a d (f x) * (w x * g x)) μ := by
    apply (hig.const_mul (1 / d)).mono' (hq.mul (hw.mul hg)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (weightSq_nonneg hd) (mul_nonneg (hw0 x) (hg0 x)))]
      exact mul_le_mul_of_nonneg_right (weightSq_le_inv hd) (mul_nonneg (hw0 x) (hg0 x))
  have hieg : Integrable (fun x => e x * (w x * g x)) μ := by
    apply (hig.const_mul E).mono' (hem.mul (hw.mul hg)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (he0 x) (mul_nonneg (hw0 x) (hg0 x)))]
      exact mul_le_mul_of_nonneg_right (heE x) (mul_nonneg (hw0 x) (hg0 x))
  have hiwg2 : Integrable (fun x => (w x * g x) ^ 2) μ := by
    apply (hiw2.mul_const (G ^ 2)).mono' ((hw.mul hg).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hg0 x) (hgG x) 2) (sq_nonneg _)
  have hwg2 : (∫ x, (w x * g x) ^ 2 ∂μ) ≤ (G * R) ^ 2 := by
    have h := integral_mono hiwg2 (hiw2.mul_const (G ^ 2)) (fun x => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hg0 x) (hgG x) 2) (sq_nonneg _))
    rw [integral_mul_const] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hw2 (sq_nonneg G)])
  have hmom := rwWeightMoments μ f hf hd hY hm hs hD
  have hDelta : 0 ≤ rwDelta a d m s := by
    unfold rwDelta rwD2 rwD4
    positivity
  exact rw_capped_average μ f (fun x => w x * g x) hd hY hDelta
    (mul_nonneg hG hR) (fun x => mul_nonneg (hw0 x) (hg0 x))
    hig hiqg hieg hmom.2.2.1 hiwg2 hrow hmom.2.2.2 hwg2

end BstLean.BlueprintLow
