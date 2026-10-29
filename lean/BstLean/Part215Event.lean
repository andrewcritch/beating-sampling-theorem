import BstLean.Part215Mixed

/-! One order-64 Markov payment controls the entire weighted input average. -/
namespace BstLean.Part215
open MeasureTheory Real Set
open scoped ENNReal

/-- A fixed positive threshold gives one complement payment. -/
theorem moment_event_charge {W : Type*} [MeasurableSpace W]
    (ν : Measure W) (F : W → ℝ≥0∞) (hF : Measurable F)
    {B δ : ℝ≥0∞} (hB : B ≠ 0) (hBt : B ≠ ∞)
    (hm : (∫⁻ a, F a ∂ν) ≤ B * δ) :
    ν {a | F a ≤ B}ᶜ ≤ δ := by
  have h := meas_ge_le_lintegral_div (μ := ν) hF.aemeasurable hB hBt
  refine (measure_mono (show {a | F a ≤ B}ᶜ ⊆ {a | B ≤ F a} from
    fun a ha => (not_le.mp (show ¬ F a ≤ B from ha)).le)).trans (h.trans ?_)
  refine (ENNReal.div_le_div_right hm B).trans_eq ?_
  rw [mul_comm B, ENNReal.mul_div_cancel_right hB hBt]

/-- The weighted average pays Markov once after integration over all inputs. -/
theorem weighted_error_event_charge {W X : Type*}
    [MeasurableSpace W] [MeasurableSpace X]
    (ν : Measure W) (μ : Measure X) [SFinite ν] [SFinite μ]
    (w : X → ℝ≥0∞) (f : W → X → ℝ)
    (hw : Measurable w) (hf : Measurable (Function.uncurry f))
    (hf0 : ∀ a x, 0 ≤ f a x) {ε B δ : ℝ≥0∞}
    (hm : ∀ x, (∫⁻ a, ENNReal.ofReal (f a x) ^ 64 ∂ν) ≤ ε ^ 64)
    (hB : B ≠ 0) (hBt : B ≠ ∞)
    (hbudget : ε ^ 64 * (∫⁻ x, w x ∂μ) ^ (8 / 3 : ℝ) ≤ B * δ) :
    ν {a | (∫⁻ x, w x * ENNReal.ofReal (f a x) ^ 24 ∂μ) ^ (8 / 3 : ℝ) ≤ B}ᶜ ≤ δ := by
  apply moment_event_charge ν _ _ hB hBt
    ((weighted_mixed_moment ν μ w f hw hf hf0 hm).trans hbudget)
  exact (Measurable.lintegral_prod_right' (ν := μ)
    ((hw.comp measurable_snd).mul (hf.ennreal_ofReal.pow_const 24))).pow_const _

#print axioms moment_event_charge
#print axioms weighted_error_event_charge
end BstLean.Part215
