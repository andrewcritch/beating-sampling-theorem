import BstLean.Part221GateArray

/-! The gate array can be integrated independently of all even row data. -/
namespace BstLean.Part221
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

theorem halfGate_array_even_lintegral {m d : ℕ} {h : Fin d → ℝ} (hh : h ≠ 0)
    {β : Type*} [MeasurableSpace β] {F : (Fin d → ℝ) → β}
    (hF : Measurable F) (hev : ∀ z, F (-z) = F z)
    (Φ : (Fin m → Bool) × (Fin m → β) → ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ Z, Φ ((fun i => halfGate h (Z i)), (fun i => F (Z i)))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) =
    ∫⁻ Z, ∫⁻ Z', Φ ((fun i => halfGate h (Z i)), (fun i => F (Z' i)))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) := by
  let μ := Measure.pi fun _ : Fin m => stdGauss (Fin d)
  let G := fun Z : Fin m → Fin d → ℝ => fun i => halfGate h (Z i)
  let H := fun Z : Fin m → Fin d → ℝ => fun i => F (Z i)
  have hG : Measurable G := measurable_pi_iff.mpr fun i =>
    (measurable_halfGate h).comp (measurable_pi_apply i)
  have hH : Measurable H := measurable_pi_iff.mpr fun i => hF.comp (measurable_pi_apply i)
  have hmap : μ.map (fun Z => (G Z, H Z)) = (μ.map G).prod (μ.map H) :=
    (halfGate_array_indep_even hh hF hev).map_prod_eq_prod_map_map
      hG.aemeasurable hH.aemeasurable
  change (∫⁻ Z, Φ (G Z, H Z) ∂μ) = ∫⁻ Z, ∫⁻ Z', Φ (G Z, H Z') ∂μ ∂μ
  rw [← lintegral_map hΦ (hG.prodMk hH), hmap,
    Measure.map_prod_map μ μ hG hH,
    lintegral_map hΦ (hG.prodMap hH)]
  exact lintegral_prod _ (hΦ.comp (hG.prodMap hH)).aemeasurable

end BstLean.Part221
