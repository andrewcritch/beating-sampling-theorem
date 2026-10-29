import BstLean.Part241Price

/-! Integrate the disjoint regular and exceptional squared prices once. -/
namespace BstLean.Part241
open MeasureTheory Real Set

/-- The measure remains unnormalized. The exceptional price is at most two. -/
theorem squared_price_partition {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {K X : Set α}
    (hK : MeasurableSet K) (hX : MeasurableSet X) {H : α → ℝ}
    (iH : IntegrableOn H K μ) {P mex : ℝ}
    (hregular : ∫ a in K \ X, H a ∂μ ≤ P)
    (hexceptional : ∀ a ∈ K ∩ X, H a ≤ 2)
    (hmass : μ.real (K ∩ X) ≤ mex) :
    ∫ a in K, H a ∂μ ≤ P + 2 * mex := by
  have hiR : IntegrableOn H (K \ X) μ := iH.mono_set diff_subset
  have hiX : IntegrableOn H (K ∩ X) μ := iH.mono_set inter_subset_left
  have hdis : Disjoint (K \ X) (K ∩ X) := by
    rw [Set.disjoint_left]
    intro a ha hb
    exact ha.2 hb.2
  have hunion : (K \ X) ∪ (K ∩ X) = K := by
    ext a
    by_cases hx : a ∈ X <;> simp [hx]
  have hsplit := setIntegral_union hdis (hK.inter hX) hiR hiX
  rw [hunion] at hsplit
  have he : ∫ a in K ∩ X, H a ∂μ ≤ 2 * μ.real (K ∩ X) := by
    have h := setIntegral_mono_on hiX (integrable_const (2 : ℝ))
      (hK.inter hX) hexceptional
    simpa [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using h
  rw [hsplit]
  linarith

/-- Take one square root after the disjoint integration. -/
theorem root_price_partition {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {K X : Set α}
    (hK : MeasurableSet K) (hX : MeasurableSet X) {H : α → ℝ}
    (iH : IntegrableOn H K μ) {P mex : ℝ}
    (hregular : ∫ a in K \ X, H a ∂μ ≤ P)
    (hexceptional : ∀ a ∈ K ∩ X, H a ≤ 2)
    (hmass : μ.real (K ∩ X) ≤ mex) :
    √(∫ a in K, H a ∂μ) ≤ √(P + 2 * mex) :=
  Real.sqrt_le_sqrt (squared_price_partition μ hK hX iH hregular hexceptional hmass)

end BstLean.Part241
