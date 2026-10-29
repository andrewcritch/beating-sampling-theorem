import BstLean.Part215Actual
import BstLean.Part215Budget
import BstLean.Part153PPs2

/-! The existing sharp Jacobian moment supplies one order-160 input event. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153
open BstLean.Part29 (stdGauss)

noncomputable def operatorHighMoment {n : ℕ} (c : Fin n → ℝ) (τ : ℝ)
    (a : AgentPair n) : ℝ≥0∞ :=
  ∫⁻ ξ, ENNReal.ofReal (Xq a c τ ξ ^ 160) ∂stdGauss (Fin n)

noncomputable def operatorBudget {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((√(n : ℝ) * jS n 160 η) ^ 320) *
    ENNReal.ofReal (∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 160 ∂stdGauss (Fin n))

noncomputable def operatorEvent {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    (δ : ℝ≥0∞) : Set (AgentPair n) :=
  {a | operatorHighMoment c τ a ≤ operatorBudget c τ η / δ}

/-- This event uses the actual order-320 tangent-Jacobian moment and the input order 160. -/
theorem operator_event_charge160 {n : ℕ} (hn : 322 ≤ n) (c : Fin n → ℝ)
    {τ η : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) {δ : ℝ≥0∞} (hδ : δ ≠ 0) (hδt : δ ≠ ∞) :
    (nuA n) (operatorEvent c τ η δ)ᶜ ≤ δ := by
  have hF : Measurable (operatorHighMoment c τ) :=
    Measurable.lintegral_prod_right' (ν := stdGauss (Fin n))
      ((measurable_Xq_joint c τ).pow_const 160).ennreal_ofReal
  have hCt : operatorBudget c τ η ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hb : (∫⁻ a, operatorHighMoment c τ a ∂nuA n) ≤ operatorBudget c τ η :=
    lintegral_Xq_le (by omega) c hτ
      (fun _ hx => lemmaPP_i_sharp (by omega) (by norm_num) hη hx)
  exact budget_event_charge (nuA n) _ hF hCt hδ hδt hb

/-- Input-order monotonicity transfers this one event to the directional order 24. -/
theorem operator_event_order24 {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    (δ : ℝ≥0∞) {a : AgentPair n} (ha : a ∈ operatorEvent c τ η δ) :
    (∫⁻ ξ, ENNReal.ofReal (Xq a c τ ξ ^ 12) ∂stdGauss (Fin n)) ^ (1 / 12 : ℝ) ≤
      (operatorBudget c τ η / δ) ^ (1 / 160 : ℝ) := by
  have hm : Measurable (fun ξ => Xq a c τ ξ) := by
    have h := (measurable_Xq_joint c τ).comp
      (show Measurable (fun ξ : Fin n → ℝ => (a, ξ)) from measurable_const.prodMk measurable_id)
    simpa only [Function.comp_def] using h
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have h := lp_mono_nat (μ := stdGauss (Fin n)) hm (Xq_nonneg a c τ)
    (q := 12) (P := 160) (by norm_num) (by norm_num)
  exact h.trans (ENNReal.rpow_le_rpow ha (by norm_num))

#print axioms operator_event_charge160
#print axioms operator_event_order24
end BstLean.Part215
