import BstLean.Part215Radius
import BstLean.Part212Inverse

/-! The paper radius coefficient supplies the sharp shared-weight error event. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153
open BstLean.Part150 (thetaC rhoC)
open BstLean.Part29 (stdGauss)

noncomputable def radiusCoefficient (n j : ℕ) (θ : ℝ) : ℝ :=
  θ / (1 - (2 * j + 2 : ℝ) * θ / n)

/-- The coefficient is R_j from the paper, in the same retained normalization. -/
theorem radiusCoefficient_identity {n j : ℕ} (hn : 2 * j + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    radiusCoefficient n j (thetaC c τ) / n =
      τ ^ 2 / (normSq c + ((n : ℝ) - 2 * j - 2) * τ ^ 2) := by
  have hnR : 2 * (j : ℝ) + 2 < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hR : 0 < normSq c + (n : ℝ) * τ ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg c) (by positivity)
  have hD : 0 < normSq c + ((n : ℝ) - 2 * j - 2) * τ ^ 2 :=
    add_pos_of_nonneg_of_pos (normSq_nonneg c) (mul_pos (by linarith) (sq_pos_of_pos hτ))
  unfold radiusCoefficient thetaC rhoC
  rw [Real.sq_sqrt hR.le]
  field_simp
  ring

theorem radius_mass_le_sharp {n : ℕ} (hn : 27 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (∫⁻ ξ, radiusWeight c τ ξ ∂stdGauss (Fin n)) ≤
      ENNReal.ofReal ((radiusCoefficient n 12 (thetaC c τ) / n) ^ 12) := by
  have he : radiusWeight c τ = fun ξ =>
      ENNReal.ofReal ((τ ^ 2 / normSq (c + τ • ξ)) ^ 12) := by
    funext ξ
    rw [radiusWeight, ← ENNReal.ofReal_pow (div_nonneg hτ.le (nrm_nonneg _)), radius_power24]
    congr 1
    rw [div_pow, ← pow_mul, div_eq_mul_inv, inv_pow]
  rw [he, radiusCoefficient_identity (by omega) c hτ]
  exact BstLean.Part212.noncentral_inverse_radius (by norm_num) (by omega) c hτ

noncomputable def sharpErrorBudget {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (BstLean.Part209.pairEpsilon n 16 (1 / 100)) ^ 64 *
    ENNReal.ofReal ((radiusCoefficient n 12 (thetaC c τ) / n) ^ 12) ^ (8 / 3 : ℝ)

noncomputable def sharpErrorEvent {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : Set (AgentPair n) :=
  {a | errorInputMoment c τ a ^ (8 / 3 : ℝ) ≤
    sharpErrorBudget c τ / ENNReal.ofReal (7 / 25000)}

/-- The paper epsilon and R_12 pay 0.00028 once, with no independence between input pairs. -/
theorem sharp_error_event_one_payment {n : ℕ} (hn : 27 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real (sharpErrorEvent c τ)ᶜ ≤ 7 / 25000 := by
  have hm : Measurable (fun p : AgentPair n × (Fin n → ℝ) =>
      radiusWeight c τ p.2 * ENNReal.ofReal (nrm (inputErrorAverage c τ p.1 p.2)) ^ 24) :=
    ((measurable_radiusWeight c τ).comp measurable_snd).mul
      ((BstLean.Part130.measurable_normSq.comp
        (measurable_inputErrorAverage c τ)).sqrt.ennreal_ofReal.pow_const 24)
  have hF : Measurable (fun a : AgentPair n => errorInputMoment c τ a ^ (8 / 3 : ℝ)) :=
    (Measurable.lintegral_prod_right' (ν := stdGauss (Fin n)) hm).pow_const _
  have hCt : sharpErrorBudget c τ ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hbudget : (∫⁻ a, errorInputMoment c τ a ^ (8 / 3 : ℝ) ∂nuA n) ≤
      sharpErrorBudget c τ :=
    (actual_weighted_error_moment64 (by omega) c τ).trans
      (mul_le_mul_right (ENNReal.rpow_le_rpow (radius_mass_le_sharp hn c hτ) (by norm_num)) _)
  have he := budget_event_charge (nuA n) _ hF hCt
    (by norm_num : ENNReal.ofReal (7 / 25000 : ℝ) ≠ 0) ENNReal.ofReal_ne_top hbudget
  have hR := ENNReal.toReal_mono (b := ENNReal.ofReal (7 / 25000 : ℝ)) ENNReal.ofReal_ne_top he
  simpa only [Measure.real, sharpErrorEvent,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 7 / 25000)] using hR

#print axioms radiusCoefficient_identity
#print axioms radius_mass_le_sharp
#print axioms sharp_error_event_one_payment

/-- Take the input norm on the same error event; no additional Markov step is used. -/
theorem sharp_error_input_norm {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    {a : AgentPair n} (ha : a ∈ sharpErrorEvent c τ) :
    errorInputMoment c τ a ^ (1 / 24 : ℝ) ≤
      (sharpErrorBudget c τ / ENNReal.ofReal (7 / 25000)) ^ (1 / 64 : ℝ) := by
  have h := ENNReal.rpow_le_rpow ha (by norm_num : (0 : ℝ) ≤ 1 / 64)
  rw [← ENNReal.rpow_mul] at h
  norm_num at h
  exact h

#print axioms sharp_error_input_norm
end BstLean.Part215
