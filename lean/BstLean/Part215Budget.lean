import BstLean.Part215Event

/-! The Markov budget includes the zero-moment case. -/
namespace BstLean.Part215
open MeasureTheory Real Set
open scoped ENNReal

/-- Divide the full mixed-moment budget by the one chosen payment. -/
theorem budget_event_charge {W : Type*} [MeasurableSpace W]
    (ν : Measure W) (F : W → ℝ≥0∞) (hF : Measurable F)
    {C δ : ℝ≥0∞} (hCt : C ≠ ∞) (hδ : δ ≠ 0) (hδt : δ ≠ ∞)
    (hm : (∫⁻ a, F a ∂ν) ≤ C) :
    ν {a | F a ≤ C / δ}ᶜ ≤ δ := by
  by_cases hC : C = 0
  · have he : (∫⁻ a, F a ∂ν) = 0 := le_antisymm (by simpa [hC] using hm) bot_le
    have hz := (lintegral_eq_zero_iff hF).mp he
    have hgood : ∀ᵐ a ∂ν, F a ≤ C / δ := by
      filter_upwards [hz] with a ha
      simp [ha, hC]
    have hn : ν {a | F a ≤ C / δ}ᶜ = 0 := by
      change ν {a | ¬ F a ≤ C / δ} = 0
      simpa only [ae_iff, mem_setOf_eq] using hgood
    rw [hn]
    exact bot_le
  · apply moment_event_charge ν F hF (ENNReal.div_ne_zero.mpr ⟨hC, hδt⟩)
      (ENNReal.div_ne_top hCt hδ)
    simpa only [ENNReal.div_mul_cancel hδ hδt] using hm

/-- Intersections add each event complement once and need no independence. -/
theorem common_event_charge {W : Type*} [MeasurableSpace W]
    (ν : Measure W) (C T E : Set W) {δC δT δE : ℝ≥0∞}
    (hC : ν Cᶜ ≤ δC) (hT : ν Tᶜ ≤ δT) (hE : ν Eᶜ ≤ δE) :
    ν (C ∩ T ∩ E)ᶜ ≤ δC + δT + δE := by
  rw [compl_inter, compl_inter]
  exact (measure_union_le _ _).trans
    (add_le_add ((measure_union_le _ _).trans (add_le_add hC hT)) hE)

#print axioms budget_event_charge
#print axioms common_event_charge
end BstLean.Part215
