import BstLean.Part253Operator

/-! The actual operator allowance holds throughout the dimension interval. -/
namespace BstLean.Part264
open Real MeasureTheory
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part215 BstLean.Part219
open BstLean.Part29 (stdGauss)

theorem jS_mono {n : ℕ} (hn : 12225 ≤ n) :
    jS n 160 0.006 ≤ jS 12225 160 0.006 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hroot : √(12225 : ℝ) ≤ √(n : ℝ) := sqrt_le_sqrt hnR
  have hroot0 : 0 < √(12225 : ℝ) := by positivity
  have hg := gaussMomConst_nonneg 160
  have h1 : n1S n 160 0.006 ≤ n1S 12225 160 0.006 := by
    unfold n1S
    gcongr
  have hb : b2S n 160 ≤ b2S 12225 160 := by
    unfold b2S
    gcongr
  have he : epsS n 160 0.006 ≤ epsS 12225 160 0.006 := by
    unfold epsS
    apply exp_le_exp.mpr
    nlinarith [sq_nonneg ((n : ℝ) - 12225)]
  have h2 : n2S n 160 0.006 ≤ n2S 12225 160 0.006 := by
    unfold n2S
    exact add_le_add h1 (mul_le_mul he hb (by unfold b2S; positivity) (exp_pos _).le)
  have hr : rcS n 160 ≤ rcS 12225 160 := by
    unfold rcS
    gcongr
  have hc : rchiS n 160 ≤ rchiS 12225 160 := by
    unfold rchiS
    gcongr
  have h20 := n2S_nonneg n 160 (by norm_num : (0 : ℝ) ≤ 0.006)
  have hr0 : 0 ≤ rcS n 160 := by unfold rcS; positivity
  have hc0 : 0 ≤ rchiS n 160 := by unfold rchiS; positivity
  unfold jS
  exact add_le_add (pow_le_pow_left₀ h20 h2 2)
    (div_le_div₀ (mul_nonneg (hr0.trans hr) (hc0.trans hc))
      (mul_le_mul hr hc hc0 (hr0.trans hr)) hroot0 hroot)

theorem inverse_product_upper {n : ℕ} (hn : 12225 ≤ n) :
    (∏ i ∈ Finset.range 160, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹) ≤
      (((n : ℝ) - 321)⁻¹) ^ 160 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ ∏ _i ∈ Finset.range 160, ((n : ℝ) - 321)⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro i hi
        have hiR : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
        apply inv_nonneg.mpr
        linarith
      · intro i hi
        have hiR : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
        apply inv_anti₀ (by linarith : (0 : ℝ) < n - 321)
        linarith
    _ = _ := by simp

theorem operator_allowance_le {n : ℕ} (hn : 12225 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    operatorAllowance c τ 0.006 (ENNReal.ofReal (1 / 20000)) ^ 2 ≤ 1.22 := by
  have hnR : (12225 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num)
  rw [BstLean.Part253.operator_squared_power]
  let I : ℝ := ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 160 ∂stdGauss (Fin n)
  have hI0 : 0 ≤ I := integral_nonneg
    (fun _ => pow_nonneg (inv_nonneg.mpr (normSq_nonneg _)) 160)
  have hI : τ ^ 320 * I ≤ (((n : ℝ) - 321)⁻¹) ^ 160 := by
    have h := (invMoment_le (by omega : 2 * 160 + 1 < n) c hτ).2
    exact h.trans (inverse_product_upper hn)
  have he : (operatorBudget c τ 0.006 / ENNReal.ofReal (1 / 20000)).toReal =
      (√(n : ℝ) * jS n 160 0.006) ^ 320 * I * 20000 := by
    unfold operatorBudget
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg
        (mul_nonneg (sqrt_nonneg _) (jS_nonneg _ _ _)) 320), ENNReal.toReal_ofReal hI0,
      ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
    dsimp [I]
    ring
  have hj := (jS_mono hn).trans BstLean.Part253.jS_upper
  have hj0 := jS_nonneg n 160 0.006
  have hp : (√(n : ℝ) * jS n 160 0.006) ^ 320 =
      ((n : ℝ) * jS n 160 0.006 ^ 2) ^ 160 := by
    rw [show 320 = 2 * 160 by rfl, pow_mul, mul_pow, sq_sqrt hn0]
  have hp1 : ((n : ℝ) * jS n 160 0.006 ^ 2) ^ 160 ≤
      ((n : ℝ) * 1.055 ^ 2) ^ 160 := by gcongr
  have hratio : (n : ℝ) / ((n : ℝ) - 321) ≤ 12225 / 11904 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < n - 321)]
    linarith
  have hratio0 : 0 ≤ (n : ℝ) / ((n : ℝ) - 321) :=
    div_nonneg hn0 (by linarith)
  rw [he, hp]
  calc
    _ = (((n : ℝ) * jS n 160 0.006 ^ 2) ^ 160 * (τ ^ 320 * I)) * 20000 := by ring
    _ ≤ (((n : ℝ) * 1.055 ^ 2) ^ 160 * (((n : ℝ) - 321)⁻¹) ^ 160) * 20000 := by
      have ht0 : 0 ≤ τ ^ 320 * I := mul_nonneg (pow_nonneg hτ.le _) hI0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hp1 hI ht0 (pow_nonneg (by positivity) 160)) (by norm_num)
    _ = ((n : ℝ) / ((n : ℝ) - 321) * 1.055 ^ 2) ^ 160 * 20000 := by
      rw [← mul_pow]
      congr 2
      simp only [div_eq_mul_inv]
      ring
    _ ≤ ((12225 / 11904 : ℝ) * 1.055 ^ 2) ^ 160 * 20000 := by gcongr
    _ ≤ (1.22 : ℝ) ^ 160 := by norm_num

end BstLean.Part264
