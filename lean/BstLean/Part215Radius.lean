import BstLean.Part215Actual
import BstLean.Part215Budget

/-! A proved coarse inverse-radius supply makes the error event unconditional. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153
open BstLean.Part29 (stdGauss)

/-- This product is a coarse radius allowance. It does not equal the paper R_j. -/
noncomputable def inverseAllowance (n j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹

lemma radius_power24 {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    (τ / nrm (c + τ • ξ)) ^ 24 =
      τ ^ 24 * (normSq (c + τ • ξ))⁻¹ ^ 12 := by
  rw [div_pow, show (24 : ℕ) = 2 * 12 by norm_num, pow_mul (nrm _), nrm_sq,
    div_eq_mul_inv, inv_pow]

theorem radius_mass_le_coarse {n : ℕ} (hn : 26 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫⁻ ξ, radiusWeight c τ ξ ∂stdGauss (Fin n)) ≤ ENNReal.ofReal (inverseAllowance n 12) := by
  obtain ⟨hi, hb⟩ := invMoment_le (p := 12) (by omega) c hτ
  have hfi := hi.const_mul (τ ^ 24)
  have hnon : ∀ ξ : Fin n → ℝ, 0 ≤ τ ^ 24 * (normSq (c + τ • ξ))⁻¹ ^ 12 :=
    fun ξ => mul_nonneg (pow_nonneg hτ.le _)
      (pow_nonneg (inv_nonneg.mpr (normSq_nonneg _)) _)
  have he : radiusWeight c τ = fun ξ =>
      ENNReal.ofReal (τ ^ 24 * (normSq (c + τ • ξ))⁻¹ ^ 12) := by
    funext ξ
    rw [radiusWeight, ← ENNReal.ofReal_pow (div_nonneg hτ.le (nrm_nonneg _)), radius_power24]
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hnon), integral_const_mul]
  exact ENNReal.ofReal_le_ofReal hb

/-- The actual error event is available with one payment from a coarse scalar radius bound. -/
theorem error_event_charge_coarse {n : ℕ} (hn : 26 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {B δ : ℝ≥0∞}
    (hB : B ≠ 0) (hBt : B ≠ ∞)
    (hbudget : ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64 *
      ENNReal.ofReal (inverseAllowance n 12) ^ (8 / 3 : ℝ) ≤ B * δ) :
    (nuA n) {a | errorInputMoment c τ a ^ (8 / 3 : ℝ) ≤ B}ᶜ ≤ δ := by
  apply actual_error_event_charge (by omega) c τ hB hBt
  exact (mul_le_mul_right
    (ENNReal.rpow_le_rpow (radius_mass_le_coarse hn c hτ) (by norm_num)) _).trans hbudget

/-- The order-64 event gives the order-24 input allowance without a second payment. -/
theorem error_event_input_bound {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) (K : ℝ≥0∞)
    (h : errorInputMoment c τ a ^ (8 / 3 : ℝ) ≤ K ^ 64) :
    errorInputMoment c τ a ≤ K ^ 24 := by
  have h' := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 3 / 8)
  rw [← ENNReal.rpow_natCast K 64] at h'
  simp only [← ENNReal.rpow_mul] at h'
  norm_num at h'
  exact h'

#print axioms radius_mass_le_coarse
#print axioms error_event_charge_coarse
#print axioms error_event_input_bound

noncomputable def coarseErrorBudget (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64 *
    ENNReal.ofReal (inverseAllowance n 12) ^ (8 / 3 : ℝ)

noncomputable def errorEvent {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Set (AgentPair n) :=
  {a | errorInputMoment c τ a ^ (8 / 3 : ℝ) ≤ coarseErrorBudget n / ENNReal.ofReal (7 / 25000)}

/-- The full shared-weight input error has conditional complement payment 0.00028. -/
theorem error_event_one_payment {n : ℕ} (hn : 26 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (errorEvent c τ)ᶜ ≤ 7 / 25000 := by
  have hm : Measurable (fun p : AgentPair n × (Fin n → ℝ) =>
      radiusWeight c τ p.2 * ENNReal.ofReal (nrm (inputErrorAverage c τ p.1 p.2)) ^ 24) :=
    ((measurable_radiusWeight c τ).comp measurable_snd).mul
      ((BstLean.Part130.measurable_normSq.comp
        (measurable_inputErrorAverage c τ)).sqrt.ennreal_ofReal.pow_const 24)
  have hF : Measurable (fun a : AgentPair n => errorInputMoment c τ a ^ (8 / 3 : ℝ)) :=
    (Measurable.lintegral_prod_right' (ν := stdGauss (Fin n)) hm).pow_const _
  have hCt : coarseErrorBudget n ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hbudget : (∫⁻ a, errorInputMoment c τ a ^ (8 / 3 : ℝ) ∂nuA n) ≤
      coarseErrorBudget n :=
    (actual_weighted_error_moment64 (by omega) c τ).trans
      (mul_le_mul_right (ENNReal.rpow_le_rpow (radius_mass_le_coarse hn c hτ) (by norm_num)) _)
  have he := budget_event_charge (nuA n) _ hF hCt
    (by norm_num : ENNReal.ofReal (7 / 25000 : ℝ) ≠ 0) ENNReal.ofReal_ne_top hbudget
  have hR := ENNReal.toReal_mono (b := ENNReal.ofReal (7 / 25000 : ℝ)) ENNReal.ofReal_ne_top he
  simpa only [Measure.real, errorEvent, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 7 / 25000)] using hR

#print axioms error_event_one_payment
end BstLean.Part215
