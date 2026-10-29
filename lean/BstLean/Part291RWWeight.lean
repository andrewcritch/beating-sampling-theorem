import BstLean.Part291RWNetwork

/-! The two reciprocal estimates needed by WS use the same original measure.
The mean estimate uses the first and second deficit moments. The row estimate
uses the second and fourth deficit moments. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real
open BstLean.Part188

noncomputable def rwDelta (a d m s : ℝ) : ℝ :=
  rwD2 m s / (a - m ^ 2) ^ 2 + rwD4 m s ^ 2 / (d * (a - m ^ 2) ^ 2)

noncomputable def rwWeightMean (a d m s : ℝ) : ℝ :=
  1 / (a - m ^ 2) + (2 * m * s + s ^ 2) / (a - m ^ 2) ^ 2 +
    rwD2 m s ^ 2 / (d * (a - m ^ 2) ^ 2)

theorem rwWeightMoments {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X → ℝ) (hf : Measurable f)
    {a d m s : ℝ} (hd : 0 < d) (hY : d < a - m ^ 2)
    (hm : 0 ≤ m) (hs : 0 ≤ s) (h : RWDeficitMoments μ f m s) :
    Integrable (fun x => weightSq a d (f x)) μ ∧
    (∫ x, weightSq a d (f x) ∂μ) ≤ rwWeightMean a d m s ∧
    Integrable (fun x => reciprocalExcess a d m (f x) ^ 2) μ ∧
    (∫ x, reciprocalExcess a d m (f x) ^ 2 ∂μ) ≤ rwDelta a d m s ^ 2 := by
  have hD2 : 0 ≤ rwD2 m s := by unfold rwD2; positivity
  have hD4 : 0 ≤ rwD4 m s := by
    unfold rwD4
    have := BstLean.Part195.rotationConstant_nonneg 2
    positivity
  have hY0 : 0 < a - m ^ 2 := hd.trans hY
  have he := reciprocalExcess_moment2 μ f hf hd hY hD2 hD4
    h.second_integrable h.fourth_integrable h.second h.fourth
  have hqm : Measurable (fun x => weightSq a d (f x)) := by
    unfold weightSq
    fun_prop
  have hqi : Integrable (fun x => weightSq a d (f x)) μ :=
    integrable_of_abs_bound μ hqm (fun x => by
      rw [abs_of_nonneg (weightSq_nonneg hd)]
      exact weightSq_le_inv hd)
  refine ⟨hqi, ?_, he.1, he.2⟩
  have he1 : Integrable (fun x => reciprocalExcess a d m (f x)) μ :=
    (h.first_integrable.div_const _).add (h.second_integrable.div_const _)
  have hb := integral_mono hqi ((integrable_const (1 / (a - m ^ 2))).add he1)
    (fun x => reciprocalExcess_bound hd hY)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const _) he1, integral_const, probReal_univ, one_smul] at hb
  unfold reciprocalExcess at hb
  rw [integral_add (h.first_integrable.div_const _) (h.second_integrable.div_const _),
    integral_div, integral_div] at hb
  unfold rwWeightMean
  exact hb.trans (by
    have h1 := div_le_div_of_nonneg_right h.first (sq_nonneg (a - m ^ 2))
    have h2 := div_le_div_of_nonneg_right h.second (by positivity : 0 ≤ d * (a - m ^ 2) ^ 2)
    linarith)

end BstLean.BlueprintLow
