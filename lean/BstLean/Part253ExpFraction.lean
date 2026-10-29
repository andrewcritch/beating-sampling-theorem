import BstLean.Part253Exp

/-! The second centre tail uses the exponent 16.8. -/
namespace BstLean.Part253
open Real

theorem exp_105_lower : (2.85765 : ℝ) ≤ exp 1.05 := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1.05) 12
  have hn : (2.85765 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1.05 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans h

theorem exp_minus_168_upper : exp (-16.8 : ℝ) ≤ 0.0000000506 := by
  have he : exp (16.8 : ℝ) = exp (1.05 : ℝ) ^ 16 := by
    convert exp_nat_mul (1.05 : ℝ) 16 using 1 <;> norm_num
  have h : (2.85765 : ℝ) ^ 16 ≤ exp (16.8 : ℝ) := by
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) exp_105_lower 16
  rw [exp_neg]
  exact ((inv_le_inv₀ (exp_pos _) (by positivity)).mpr h).trans (by norm_num)

end BstLean.Part253
