import BstLean.Part219Junction
import BstLean.Part219PaperIdeal
import BstLean.Part219Formula

/-! The computed-centre directional moment has the paper ideal term and one error payment. -/
namespace BstLean.Part219
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (thetaC)

noncomputable def paperDirectionBudget {n : ℕ} (c : Fin n → ℝ) (τ e ξhp η : ℝ)
    (δ : ℝ≥0∞) : ℝ :=
  (paperIdeal n (thetaC c τ) e +
    BstLean.Part209.pairEpsilon n 16 (1 / 100) *
      √(radiusCoefficient n 12 (thetaC c τ) / e) / ((7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) +
    √(operatorAllowance c τ η δ ^ 2 * ξhp / ((n : ℝ) * e))) ^ 2

theorem paperDirectionBudget_identity {n : ℕ} (hn : 195 ≤ n) (c : Fin n → ℝ)
    {τ e ξhp η : ℝ} (hτ : 0 < τ) (he : 0 < e) (δ : ℝ≥0∞) :
    directionalBudget n e ξhp (paperInputAllowance n (thetaC c τ))
      (errorAllowance c τ) (operatorAllowance c τ η δ) = paperDirectionBudget c τ e ξhp η δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have hE : √e ≠ 0 := (sqrt_pos.mpr he).ne'
  have hR := radiusCoefficient_nonneg (j := 12) (by omega) c hτ
  have hR' : 0 ≤ radiusCoefficient n 12 (thetaC c τ) := by
    simpa only [zero_mul, div_mul_cancel₀ _ hnR.ne'] using
      mul_le_mul_of_nonneg_right hR hnR.le
  have hO : 0 ≤ operatorAllowance c τ η δ := mul_nonneg hτ.le ENNReal.toReal_nonneg
  have herr : (√(n : ℝ) / √e) * errorAllowance c τ =
      BstLean.Part209.pairEpsilon n 16 (1 / 100) *
        √(radiusCoefficient n 12 (thetaC c τ) / e) / ((7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) := by
    rw [errorAllowance_formula (by omega) c hτ, sqrt_div hR', sqrt_div hR']
    field_simp
    <;> ring
  have hop : √(ξhp / ((n : ℝ) * e)) * operatorAllowance c τ η δ =
      √(operatorAllowance c τ η δ ^ 2 * ξhp / ((n : ℝ) * e)) := by
    rw [mul_div_assoc, sqrt_mul (sq_nonneg _), sqrt_sq hO, mul_comm]
  unfold directionalBudget paperDirectionBudget
  rw [paperIdeal_identity hn c hτ he, herr, hop]

/-- The ideal estimate is proved internally. The premises are the centre and operator events. -/
theorem directionMoment_paper {n : ℕ} (hn : 195 ≤ n)
    (D : BstLean.Part157.Design n) (c : BstLean.Part157.Ret n)
    (hτ : 0 < D.tau0 c) {e ξhp η : ℝ} {δ : ℝ≥0∞}
    (he : 0 < e) (hξ : 0 ≤ ξhp) (hδ : δ ≠ 0)
    (hq : 1 - thetaC c.1.2 (D.tau0 c) ∈ Icc (0 : ℝ) (27 / 50))
    (hb : (n : ℝ) * e ≤ normSq (D.bA c.1 c.2.1.1))
    (hfull : normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ ξhp)
    (herr : c.2.1.1 ∈ sharpErrorEvent c.1.2 (D.tau0 c))
    (hop : c.2.1.1 ∈ operatorEvent c.1.2 (D.tau0 c) η δ) :
    BstLean.Part188.DirectionMoment D c
      (paperDirectionBudget c.1.2 (D.tau0 c) e ξhp η δ) := by
  have h := directionMoment_on_events (by omega) D c hτ he hξ
    (paperInputAllowance_nonneg hn c.1.2 hτ) hδ hb hfull
    (ideal_norm_paper hn c.1.2 hτ hq) herr hop
  rw [paperDirectionBudget_identity hn c.1.2 hτ he δ] at h
  exact h

/-- A proved scalar upper bound, including a window supremum bound, enlarges the same moment. -/
theorem directionMoment_mono {n : ℕ} {D : BstLean.Part157.Design n}
    {c : BstLean.Part157.Ret n} {M M' : ℝ}
    (h : BstLean.Part188.DirectionMoment D c M) (hMM : M ≤ M') :
    BstLean.Part188.DirectionMoment D c M' := by
  exact ⟨h.1.trans hMM, h.2.1, h.2.2.trans
    (pow_le_pow_left₀ (div_nonneg h.1 (Nat.cast_nonneg n))
      (div_le_div_of_nonneg_right hMM (Nat.cast_nonneg n)) 12)⟩

#print axioms paperDirectionBudget_identity
#print axioms directionMoment_paper
#print axioms directionMoment_mono
#check directionMoment_paper
end BstLean.Part219
