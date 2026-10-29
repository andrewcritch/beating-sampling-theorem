import BstLean.Part220Charge

namespace BstLean.Part252
open MeasureTheory Set
open scoped ENNReal

theorem product_charge_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (σ : Measure Y) [IsProbabilityMeasure σ]
    {E : Set X} (hE : MeasurableSet E) {T : Set (X × Y)} (hT : MeasurableSet T)
    {δE δ : ℝ} (hδE : 0 ≤ δE) (hδ : 0 ≤ δ)
    (hfirst : μ.real Eᶜ ≤ δE)
    (hcond : ∀ᵐ x ∂μ, x ∈ E → σ {y | (x, y) ∈ T} ≤ ENNReal.ofReal δ) :
    (μ.prod σ).real T ≤ δE + δ := by
  have hfirst' : μ Eᶜ ≤ ENNReal.ofReal δE := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ Eᶜ)]
    exact ENNReal.ofReal_le_ofReal hfirst
  apply ENNReal.toReal_le_of_le_ofReal (add_nonneg hδE hδ)
  rw [Measure.prod_apply hT, ENNReal.ofReal_add hδE hδ]
  calc
    _ ≤ ∫⁻ x, Eᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x + ENNReal.ofReal δ ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hcond] with x hx
      change σ {y | (x, y) ∈ T} ≤ _
      by_cases he : x ∈ E
      · simpa [Set.indicator, he, Set.preimage] using hx he
      · have hσ : σ {y | (x, y) ∈ T} ≤ 1 :=
          (measure_mono (subset_univ _)).trans_eq (measure_univ)
        exact hσ.trans (by simp [Set.indicator, he])
    _ = μ Eᶜ + ENNReal.ofReal δ := by
      rw [lintegral_add_left (measurable_const.indicator hE.compl)]
      simp [lintegral_indicator hE.compl]
    _ ≤ _ := add_le_add hfirst' le_rfl

end BstLean.Part252
