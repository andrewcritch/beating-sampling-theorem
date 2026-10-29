import BstLean.Part253OperatorConstants

/-! The actual Part219 operator allowance has the scalar cap used by the local centres. -/
namespace BstLean.Part253
open Real MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part215 BstLean.Part219
open BstLean.Part29 (stdGauss)

theorem operator_squared_power {n : ℕ} (c : Fin n → ℝ) (τ η : ℝ) (δ : ℝ≥0∞) :
    (operatorAllowance c τ η δ ^ 2) ^ 160 =
      τ ^ 320 * (operatorBudget c τ η / δ).toReal := by
  rw [← pow_mul]
  unfold operatorAllowance
  rw [mul_pow, ← ENNReal.toReal_pow]
  have h := enn_root_pow (operatorBudget c τ η / δ) (by norm_num : 0 < (320 : ℕ))
  simp only [Nat.cast_ofNat] at h
  rw [h]

theorem inverse_product_upper :
    (∏ i ∈ Finset.range 160, ((12225 : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹) ≤
      ((11904 : ℝ)⁻¹) ^ 160 := by
  calc
    _ ≤ ∏ _i ∈ Finset.range 160, (11904 : ℝ)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hiR : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
        apply inv_nonneg.mpr
        linarith
      · intro i hi
        have hiR : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
        apply inv_anti₀ (by norm_num : (0 : ℝ) < 11904)
        linarith
    _ = _ := by simp

theorem operator_allowance_le (c : Fin 12225 → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ 1.22 := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num)
  rw [operator_squared_power]
  let I : ℝ := ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 160 ∂stdGauss (Fin 12225)
  have hI0 : 0 ≤ I := integral_nonneg
    (fun _ => pow_nonneg (inv_nonneg.mpr (normSq_nonneg _)) 160)
  have hI : τ ^ 320 * I ≤ ((11904 : ℝ)⁻¹) ^ 160 := by
    have h := (invMoment_le (by norm_num : 2 * 160 + 1 < 12225) c hτ).2
    exact h.trans inverse_product_upper
  have he : (operatorBudget c τ 0.006 / ENNReal.ofReal (1 / 20000)).toReal =
      (√(12225 : ℝ) * jS 12225 160 0.006) ^ 320 * I * 20000 := by
    unfold operatorBudget
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg
        (mul_nonneg (sqrt_nonneg _) (jS_nonneg _ _ _)) 320), ENNReal.toReal_ofReal hI0,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
    dsimp [I]
    ring
  have hj := jS_upper
  have hj0 := jS_nonneg 12225 160 0.006
  have hp : (√(12225 : ℝ) * jS 12225 160 0.006) ^ 320 =
      ((12225 : ℝ) * jS 12225 160 0.006 ^ 2) ^ 160 := by
    rw [show 320 = 2 * 160 by rfl, pow_mul, mul_pow, sq_sqrt (by norm_num)]
  have hp0 : 0 ≤ ((12225 : ℝ) * jS 12225 160 0.006 ^ 2) ^ 160 :=
    pow_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) 160
  have hp1 : ((12225 : ℝ) * jS 12225 160 0.006 ^ 2) ^ 160 ≤
      ((12225 : ℝ) * 1.055 ^ 2) ^ 160 := by gcongr
  rw [he, hp]
  calc
    _ = (((12225 : ℝ) * jS 12225 160 0.006 ^ 2) ^ 160 * (τ ^ 320 * I)) * 20000 := by
      ring
    _ ≤ (((12225 : ℝ) * 1.055 ^ 2) ^ 160 * ((11904 : ℝ)⁻¹) ^ 160) * 20000 := by
      have ht0 : 0 ≤ τ ^ 320 * I := mul_nonneg (pow_nonneg hτ.le _) hI0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hp1 hI ht0 (pow_nonneg (by norm_num) 160)) (by norm_num)
    _ ≤ (1.22 : ℝ) ^ 160 := by norm_num

end BstLean.Part253
