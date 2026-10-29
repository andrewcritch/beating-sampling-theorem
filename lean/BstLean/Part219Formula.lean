import BstLean.Part219Events

/-! The realized error allowance equals the paper's epsilon and inverse-radius expression. -/
namespace BstLean.Part219
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part150 (thetaC)

lemma radiusCoefficient_nonneg {n j : ℕ} (hn : 2 * j + 2 < n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 ≤ radiusCoefficient n j (thetaC c τ) / n := by
  rw [radiusCoefficient_identity hn c hτ]
  have hnR : 2 * (j : ℝ) + 2 < n := by exact_mod_cast hn
  exact div_nonneg (sq_nonneg _) (add_nonneg (normSq_nonneg _)
    (mul_nonneg (by linarith) (sq_nonneg _)))

/-- Taking the event root introduces no extra constant or probability payment. -/
theorem errorAllowance_formula {n : ℕ} (hn : 27 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    errorAllowance c τ =
      BstLean.Part209.pairEpsilon n 16 (1 / 100) *
        √(radiusCoefficient n 12 (thetaC c τ) / n) / ((7 / 25000 : ℝ) ^ (1 / 64 : ℝ)) := by
  have hε : 0 ≤ BstLean.Part209.pairEpsilon n 16 (1 / 100) :=
    add_nonneg (BstLean.Part209.meanEpsilon_nonneg n 16 (by norm_num) (by norm_num))
      (BstLean.Part209.fluctuationRoot_nonneg n 16)
  have hR := radiusCoefficient_nonneg (j := 12) (by omega) c hτ
  unfold errorAllowance sharpErrorBudget
  rw [ENNReal.ofReal_pow hR, ENNReal.div_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hε, ENNReal.toReal_ofReal hR,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 7 / 25000), ← sqrt_eq_rpow]
  rw [sqrt_div' _ (Nat.cast_nonneg n)]

#print axioms errorAllowance_formula
end BstLean.Part219
