import BstLean.Part188Weight

namespace BstLean.Part188

open MeasureTheory Real

lemma square_deficit_bound {f mu m : ℝ} (hmu0 : 0 ≤ mu) (hmu : mu ≤ m) :
    max (f ^ 2 - m ^ 2) 0 ≤ 2 * m * |f - mu| + (f - mu) ^ 2 := by
  have hm : 0 ≤ m := hmu0.trans hmu
  have hsq : mu ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hmu0 hmu 2
  have h1 : mu * (f - mu) ≤ mu * |f - mu| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hmu0
  have h2 : mu * |f - mu| ≤ m * |f - mu| :=
    mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
  apply max_le
  · nlinarith
  · positivity


/-- Integrate the capped reciprocal bound without an independence assumption. -/
theorem reciprocal_weight_mean {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) {a d m U V : ℝ}
    (hd : 0 < d) (hY : d < a - m ^ 2)
    (hiq : Integrable (fun x => weightSq a d (f x)) μ)
    (hiD : Integrable (fun x => max (f x ^ 2 - m ^ 2) 0) μ)
    (hiD2 : Integrable (fun x => (max (f x ^ 2 - m ^ 2) 0) ^ 2) μ)
    (hD : ∫ x, max (f x ^ 2 - m ^ 2) 0 ∂μ ≤ U)
    (hD2 : ∫ x, (max (f x ^ 2 - m ^ 2) 0) ^ 2 ∂μ ≤ V) :
    ∫ x, weightSq a d (f x) ∂μ ≤
      1 / (a - m ^ 2) + U / (a - m ^ 2) ^ 2 + V / (d * (a - m ^ 2) ^ 2) := by
  have hi := ((integrable_const (1 / (a - m ^ 2))).add
    (hiD.div_const ((a - m ^ 2) ^ 2))).add (hiD2.div_const (d * (a - m ^ 2) ^ 2))
  have h := integral_mono hiq hi (fun x => reciprocal_weight_bound hd hY)
  dsimp only [Pi.add_apply] at h
  rw [integral_add, integral_add, integral_const, probReal_univ, one_smul,
    integral_div, integral_div] at h
  · exact h.trans (add_le_add
      (add_le_add le_rfl (div_le_div_of_nonneg_right hD (sq_nonneg _)))
      (div_le_div_of_nonneg_right hD2 (by positivity)))
  all_goals first | exact integrable_const _ | exact hiD.div_const _ |
    exact hiD2.div_const _ | exact (integrable_const _).add (hiD.div_const _)

end BstLean.Part188
