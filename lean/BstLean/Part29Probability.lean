import Mathlib

/-!
# Part 29, layer L3: the probability combination

`proofs/option-m/29-explicit-22-at-100.tex`, Lemma (exact normalization), last step. `E` is the
numerator of a branch's error, with `∫ E² ≤ σ²`; `Y` is the parity floor, with `P{Y < y₀} ≤ η`.
Chebyshev on `E` with failure `q = δ − η`, and a union bound, give the good event with probability at
least `1 − δ`; on it, `E² / Y ≤ σ² / (q y₀)`.
-/

namespace BstLean.Part29

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The bad event (floor fails, or Chebyshev fails) has probability at most `δ`. -/
theorem chebyshev_floor (P : Measure Ω) [IsProbabilityMeasure P] (E Y : Ω → ℝ)
    (hE : AEMeasurable E P) (hE2 : Integrable (fun ω => E ω ^ 2) P)
    (σ2 y0 η δ : ℝ) (hσ : 0 < σ2) (hη : 0 ≤ η) (hηδ : η < δ)
    (hint : ∫ ω, E ω ^ 2 ∂P ≤ σ2)
    (hY : P {ω | Y ω < y0} ≤ ENNReal.ofReal η) :
    P {ω | ¬ (y0 ≤ Y ω ∧ E ω ^ 2 ≤ σ2 / (δ - η))} ≤ ENNReal.ofReal δ := by
  have hq : 0 < δ - η := sub_pos.mpr hηδ
  have hc : 0 < σ2 / (δ - η) := div_pos hσ hq
  have hi : Integrable (fun ω => E ω ^ 2 / (σ2 / (δ - η))) P :=
    hE2.div_const _
  have hb : P {ω | σ2 / (δ - η) < E ω ^ 2} ≤ ENNReal.ofReal (δ - η) := by
    refine (hi.measure_le_integral (Filter.Eventually.of_forall fun ω =>
      div_nonneg (sq_nonneg _) hc.le) ?_).trans ?_
    · intro ω hω
      exact (le_div_iff₀ hc).mpr (by simpa using hω.le)
    · apply ENNReal.ofReal_le_ofReal
      rw [integral_div]
      calc
        (∫ ω, E ω ^ 2 ∂P) / (σ2 / (δ - η)) ≤ σ2 / (σ2 / (δ - η)) :=
          div_le_div_of_nonneg_right hint hc.le
        _ = δ - η := by field_simp
  have hs : {ω | ¬ (y0 ≤ Y ω ∧ E ω ^ 2 ≤ σ2 / (δ - η))} =
      {ω | Y ω < y0} ∪ {ω | σ2 / (δ - η) < E ω ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or, not_le]
  rw [hs]
  calc
    P ({ω | Y ω < y0} ∪ {ω | σ2 / (δ - η) < E ω ^ 2}) ≤
        P {ω | Y ω < y0} + P {ω | σ2 / (δ - η) < E ω ^ 2} := measure_union_le _ _
    _ ≤ ENNReal.ofReal η + ENNReal.ofReal (δ - η) := add_le_add hY hb
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add hη hq.le]
      congr 1
      ring

/-- On the good event, the error-to-floor ratio is bounded. -/
theorem ratio_on_good (σ2 y0 η δ e y : ℝ) (hy0 : 0 < y0) (hηδ : η < δ)
    (hgood : y0 ≤ y ∧ e ^ 2 ≤ σ2 / (δ - η)) :
    e ^ 2 / y ≤ σ2 / ((δ - η) * y0) := by
  have hy : 0 < y := lt_of_lt_of_le hy0 hgood.1
  calc
    e ^ 2 / y ≤ e ^ 2 / y0 := div_le_div_of_nonneg_left (sq_nonneg e) hy0 hgood.1
    _ ≤ (σ2 / (δ - η)) / y0 := div_le_div_of_nonneg_right hgood.2 hy0.le
    _ = σ2 / ((δ - η) * y0) := by rw [div_div]

end BstLean.Part29
