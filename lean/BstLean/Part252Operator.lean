import BstLean.Part222CentreSource
import BstLean.Part245Moment

/-! The order-160 operator event also supplies the fourth-moment input.
This implication does not add a probability payment. -/
namespace BstLean.Part252
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

theorem fourth_on_operator_event {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) {a : AgentPair n}
    (ha : a ∈ operatorEvent c τ η δ) :
    Xi4 a.1 a.2 c τ ≤ BstLean.Part222.operatorXiAllowance c τ η δ := by
  have hm : Measurable (fun ξ => Xq a c τ ξ) := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_Xq_joint c τ).comp (measurable_const.prodMk measurable_id)
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by
    unfold stdGauss
    infer_instance
  have h0 : 0 ≤ ∫ ξ, Xq a c τ ξ ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => sq_nonneg _
  have h1 := ofReal_integral_le_lintegral (μ := stdGauss (Fin n))
    (fun ξ => sq_nonneg (Xq a c τ ξ))
  have h2 := lp_mono_nat (μ := stdGauss (Fin n)) hm (Xq_nonneg a c τ)
    (q := 2) (P := 160) (by norm_num) (by norm_num)
  have h3 : ENNReal.ofReal (√(∫ ξ, Xq a c τ ξ ^ 2 ∂stdGauss (Fin n))) ≤
      (operatorBudget c τ η / δ) ^ (1 / 160 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num)]
    exact (ENNReal.rpow_le_rpow h1 (by norm_num)).trans
      (h2.trans (ENNReal.rpow_le_rpow ha (by norm_num)))
  have ht : (operatorBudget c τ η / δ) ^ (1 / 160 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top) hδ)
  have h4 := ENNReal.toReal_mono ht h3
  rw [ENNReal.toReal_ofReal (sqrt_nonneg _)] at h4
  have he : (fun ξ : Fin n → ℝ =>
      BstLean.Part152.opN (jacT a.1 a.2 (sphPt (c + τ • ξ))) ^ 4 *
        (normSq (c + τ • ξ))⁻¹ ^ 2) = fun ξ => Xq a c τ ξ ^ 2 := by
    funext ξ
    unfold Xq
    ring
  unfold Xi4 BstLean.Part222.operatorXiAllowance
  rw [he]
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

theorem fourth_of_operator_cap {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    {δ : ℝ≥0∞} (hδ : δ ≠ 0) {a : AgentPair n}
    (ha : a ∈ operatorEvent c τ η δ)
    (hcap : BstLean.Part219.operatorAllowance c τ η δ ^ 2 ≤ 13 / 10) :
    ((c, τ), a) ∈ BstLean.Part245.MomentM12 n := by
  exact (fourth_on_operator_event c τ η hδ ha).trans
    (BstLean.Part222.operatorXiAllowance_le c τ η (13 / 10) δ hcap)

/-- The normalized budget has the same units as the paper's operator coefficient. -/
noncomputable def operatorCoefficient {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ)
    (δ : ℝ≥0∞) : ℝ :=
  τ ^ 2 * ((operatorBudget c τ η / δ) ^ (1 / 160 : ℝ)).toReal

theorem operatorCoefficient_eq {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ) (δ : ℝ≥0∞) :
    operatorCoefficient c τ η δ = BstLean.Part219.operatorAllowance c τ η δ ^ 2 := by
  unfold operatorCoefficient BstLean.Part219.operatorAllowance
  rw [mul_pow, ← ENNReal.toReal_pow, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

theorem operatorCoefficient_power {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ) (δ : ℝ≥0∞) :
    operatorCoefficient c τ η δ ^ 160 =
      τ ^ 320 * (operatorBudget c τ η / δ).toReal := by
  unfold operatorCoefficient
  rw [mul_pow, ← pow_mul, ← ENNReal.toReal_pow]
  have he := BstLean.Part152.enn_root_pow (operatorBudget c τ η / δ)
    (by norm_num : 0 < (160 : ℕ))
  norm_num only [Nat.cast_ofNat] at he
  rw [he]

end BstLean.Part252
