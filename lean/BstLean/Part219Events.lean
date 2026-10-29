import BstLean.Part219Norm
import BstLean.Part215SharpRadius

/-! The two existing events supply finite input norms, without new probability payments. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

lemma errorSize_norm_power {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (a : AgentPair n) :
    eLpNorm (errorSize c τ a) 24 (stdGauss (Fin n)) ^ 24 = errorInputMoment c τ a := by
  have hp := eLpNorm_nat_pow (μ := stdGauss (Fin n)) (by norm_num : (24 : ℕ) ≠ 0)
    (measurable_errorSize c τ a).aestronglyMeasurable
  norm_num only [Nat.cast_ofNat] at hp
  rw [hp]
  apply lintegral_congr
  intro x
  have h0 : 0 ≤ errorSize c τ a x := mul_nonneg (radial_nonneg c hτ x) (nrm_nonneg _)
  rw [abs_of_nonneg h0]
  change ENNReal.ofReal ((radial c τ x * nrm (inputErrorAverage c τ a x)) ^ 24) =
    ENNReal.ofReal (radial c τ x) ^ 24 * ENNReal.ofReal (nrm (inputErrorAverage c τ a x)) ^ 24
  rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg (radial_nonneg c hτ x) 24),
    ENNReal.ofReal_pow (radial_nonneg c hτ x), ENNReal.ofReal_pow (nrm_nonneg _)]

noncomputable def errorAllowance {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ((sharpErrorBudget c τ / ENNReal.ofReal (7 / 25000)) ^ (1 / 64 : ℝ)).toReal

lemma errorAllowance_finite {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) :
    (sharpErrorBudget c τ / ENNReal.ofReal (7 / 25000)) ^ (1 / 64 : ℝ) ≠ ∞ := by
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  apply ENNReal.div_ne_top
  · unfold sharpErrorBudget
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  · norm_num

/-- The sharp shared-weight event supplies its order-24 norm on the same event. -/
theorem error_norm_on_event {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    {a : AgentPair n} (ha : a ∈ sharpErrorEvent c τ) :
    eLpNorm (errorSize c τ a) 24 (stdGauss (Fin n)) ≤ ENNReal.ofReal (errorAllowance c τ) := by
  have h := sharp_error_input_norm c τ ha
  rw [← errorSize_norm_power c hτ a, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
  norm_num at h
  simpa only [errorAllowance, ENNReal.ofReal_toReal (errorAllowance_finite c τ)] using h

lemma operatorSize_sq {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (a : AgentPair n) (x) :
    operatorSize c τ a x ^ 2 = τ ^ 2 * Xq a c τ x := by
  simp only [operatorSize, radial, mul_pow, div_pow, nrm_sq, Xq, standPoint]
  ring

lemma operatorSize_norm_power {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (a : AgentPair n) :
    eLpNorm (operatorSize c τ a) 24 (stdGauss (Fin n)) ^ 24 =
      ENNReal.ofReal τ ^ 24 *
        ∫⁻ x, ENNReal.ofReal (Xq a c τ x ^ 12) ∂stdGauss (Fin n) := by
  have hp := eLpNorm_nat_pow (μ := stdGauss (Fin n)) (by norm_num : (24 : ℕ) ≠ 0)
    (measurable_operatorSize c τ a).aestronglyMeasurable
  norm_num only [Nat.cast_ofNat] at hp
  rw [hp]
  have hm : Measurable (fun x => ENNReal.ofReal (Xq a c τ x ^ 12)) := by
    have h := (measurable_Xq_joint c τ).comp
      (show Measurable (fun x : Fin n → ℝ => (a, x)) from
        measurable_const.prodMk measurable_id)
    exact (h.pow_const 12).ennreal_ofReal
  rw [← lintegral_const_mul _ hm]
  apply lintegral_congr
  intro x
  have h0 : 0 ≤ operatorSize c τ a x := mul_nonneg (radial_nonneg c hτ x) (opN_nonneg _)
  rw [abs_of_nonneg h0]
  have hp : operatorSize c τ a x ^ 24 = τ ^ 24 * Xq a c τ x ^ 12 := by
    calc
      _ = (operatorSize c τ a x ^ 2) ^ 12 := by rw [← pow_mul]
      _ = _ := by rw [operatorSize_sq, mul_pow, ← pow_mul]
  rw [hp, ENNReal.ofReal_mul (pow_nonneg hτ 24), ENNReal.ofReal_pow hτ]

noncomputable def operatorAllowance {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    (δ : ℝ≥0∞) : ℝ :=
  τ * ((operatorBudget c τ η / δ) ^ (1 / 320 : ℝ)).toReal

lemma operatorAllowance_finite {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    (operatorBudget c τ η / δ) ^ (1 / 320 : ℝ) ≠ ∞ := by
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  apply ENNReal.div_ne_top _ hδ
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

/-- The order-160 operator event supplies order 24 in the directional normalization. -/
theorem operator_norm_on_event {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (η : ℝ) {δ : ℝ≥0∞} (hδ : δ ≠ 0)
    {a : AgentPair n} (ha : a ∈ operatorEvent c τ η δ) :
    eLpNorm (operatorSize c τ a) 24 (stdGauss (Fin n)) ≤
      ENNReal.ofReal (operatorAllowance c τ η δ) := by
  have h := ENNReal.rpow_le_rpow (operator_event_order24 c τ η δ ha)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [← ENNReal.rpow_mul] at h
  norm_num at h
  have he := congrArg (fun v : ℝ≥0∞ => v ^ (1 / 24 : ℝ))
    (operatorSize_norm_power c hτ a)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at he
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at he
  norm_num at he
  rw [he]
  have hh := mul_le_mul_right h (ENNReal.ofReal τ)
  simpa only [operatorAllowance, ENNReal.ofReal_mul hτ,
    ENNReal.ofReal_toReal (operatorAllowance_finite c τ η hδ)] using hh

#print axioms error_norm_on_event
#print axioms operator_norm_on_event
end BstLean.Part219
