import Mathlib

/-!
# Part 149: two rearrangements of iterated integrals (Tonelli)

Do not use `sorry`, `native_decide` or `axiom`.

* `lint_assoc3`: `∫⁻ over μa ⊗ (μb ⊗ μc)` as `∫⁻ over (μa ⊗ μb)` of `∫⁻ over μc`.
* `lint_assoc4`: `∫⁻ over (μa ⊗ (μb ⊗ μc)) ⊗ μd` as `∫⁻ over (μa ⊗ μb)` of `∫⁻ over (μc ⊗ μd)`.
-/

namespace BstLean.Part149

open MeasureTheory
open scoped ENNReal

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

lemma lint_assoc3 (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb]
    [SFinite μc] {g : α × β × γ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂(μa.prod (μb.prod μc)) =
      ∫⁻ x, ∫⁻ z, g (x.1, x.2, z) ∂μc ∂(μa.prod μb) := by
  have h1 : Measurable (fun q : (α × β) × γ => g (q.1.1, q.1.2, q.2)) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  rw [lintegral_prod _ hg.aemeasurable, lintegral_prod _ h1.lintegral_prod_right'.aemeasurable]
  refine lintegral_congr fun a => ?_
  have h2 : Measurable (fun q : β × γ => g (a, q)) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ h2.aemeasurable]

lemma lint_assoc4 (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] {g : (α × β × γ) × δ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ p, g p ∂((μa.prod (μb.prod μc)).prod μd) =
      ∫⁻ x, ∫⁻ y, g ((x.1, x.2, y.1), y.2) ∂(μc.prod μd) ∂(μa.prod μb) := by
  have h0 : Measurable (fun p : α × β × γ => ∫⁻ d, g (p, d) ∂μd) := hg.lintegral_prod_right'
  rw [lintegral_prod _ hg.aemeasurable, lint_assoc3 μa μb μc h0]
  refine lintegral_congr fun x => ?_
  have h2 : Measurable (fun y : γ × δ => g ((x.1, x.2, y.1), y.2)) :=
    hg.comp ((measurable_const.prodMk (measurable_const.prodMk measurable_fst)).prodMk
      measurable_snd)
  rw [lintegral_prod _ h2.aemeasurable]

end BstLean.Part149
