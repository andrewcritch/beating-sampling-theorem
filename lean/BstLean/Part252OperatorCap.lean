import BstLean.Part252Operator
import BstLean.Part153PPs3

namespace BstLean.Part252
open MeasureTheory Real
open scoped ENNReal
open BstLean.Part130 BstLean.Part153 BstLean.Part215
open BstLean.Part29 (stdGauss)

theorem operator_cap {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    BstLean.Part219.operatorAllowance c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 2
      ≤ 127 / 100 := by
  rw [← operatorCoefficient_eq]
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 321 := by linarith
  let j := jS n 160 (6 / 1000)
  let I := ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 160 ∂stdGauss (Fin n)
  have hI : 0 ≤ I := integral_nonneg fun ξ => by positivity
  have hj0 : 0 ≤ j := jS_nonneg _ _ _
  have hj : j ≤ 10692 / 10000 := jS_160_le hn
  have hinv : τ ^ 320 * I ≤ ((n : ℝ) - 321)⁻¹ ^ 160 := by
    refine (invMoment_le (p := 160) (by omega) c hτ).2.trans ?_
    calc
      (∏ i ∈ Finset.range 160, ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹)
          ≤ ∏ _i ∈ Finset.range 160, ((n : ℝ) - 321)⁻¹ := by
        refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
        · have hi' : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
          exact inv_nonneg.mpr (by linarith)
        · have hi' : (i : ℝ) + 1 ≤ 160 := by exact_mod_cast Finset.mem_range.mp hi
          exact inv_anti₀ hd (by linarith)
      _ = _ := by simp
  have he : operatorCoefficient c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 160 =
      20000 * ((n : ℝ) * j ^ 2) ^ 160 * (τ ^ 320 * I) := by
    rw [operatorCoefficient_power]
    unfold operatorBudget
    rw [ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg (mul_nonneg (sqrt_nonneg _) hj0) 320),
      ENNReal.toReal_ofReal hI]
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
    have hs : (√(n : ℝ) * j) ^ 320 = ((n : ℝ) * j ^ 2) ^ 160 := by
      rw [show (320 : ℕ) = 2 * 160 by norm_num, pow_mul, mul_pow, sq_sqrt (by positivity)]
    change τ ^ 320 * (((√(n : ℝ) * j) ^ 320 * I) / (1 / 20000)) = _
    rw [hs]
    ring
  have hj2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : (n : ℝ) * j ^ 2 / ((n : ℝ) - 321) ≤ (127 / 100) * (15 / 16) := by
    rw [div_le_iff₀ hd]
    have hh := mul_le_mul_of_nonneg_left hj2 (by positivity : (0 : ℝ) ≤ n)
    nlinarith
  have hpow : operatorCoefficient c τ (6 / 1000) (ENNReal.ofReal (1 / 20000)) ^ 160
      ≤ (127 / 100 : ℝ) ^ 160 := by
    rw [he]
    calc
      20000 * ((n : ℝ) * j ^ 2) ^ 160 * (τ ^ 320 * I)
          ≤ 20000 * ((n : ℝ) * j ^ 2) ^ 160 * ((n : ℝ) - 321)⁻¹ ^ 160 :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg (by norm_num)
          (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg j)) 160))
      _ = 20000 * ((n : ℝ) * j ^ 2 / ((n : ℝ) - 321)) ^ 160 := by
        rw [div_eq_mul_inv, mul_pow]
        ring
      _ ≤ 20000 * ((127 / 100) * (15 / 16) : ℝ) ^ 160 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio 160) (by norm_num)
      _ ≤ (127 / 100 : ℝ) ^ 160 := by norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 127 / 100) hpow

theorem fourth_on_operator_event_8192 {n : ℕ} (hn : 8192 ≤ n)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {a : AgentPair n}
    (ha : a ∈ operatorEvent c τ (6 / 1000) (ENNReal.ofReal (1 / 20000))) :
    ((c, τ), a) ∈ BstLean.Part245.MomentM12 n :=
  fourth_of_operator_cap c τ (6 / 1000) (by norm_num) ha
    ((operator_cap hn c hτ).trans (by norm_num))

end BstLean.Part252
