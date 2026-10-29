import BstLean.Part253Roots

/-! Rational exponential bounds for the centre certificate. -/
namespace BstLean.Part253
open Real

theorem exp_one_lower : (2.71828 : ℝ) ≤ exp 1 := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 12
  have hn : (2.71828 : ℝ) ≤ ∑ i ∈ Finset.range 12, (1 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans h

theorem exp_negative_bound (n : ℕ) {B : ℝ}
    (hB : ((2.71828 : ℝ) ^ n)⁻¹ ≤ B) : exp (-(n : ℝ)) ≤ B := by
  have h : (2.71828 : ℝ) ^ n ≤ exp (n : ℝ) := by
    have he : exp (n : ℝ) = exp (1 : ℝ) ^ n := by
      simpa only [mul_one] using exp_nat_mul (1 : ℝ) n
    rw [he]
    exact pow_le_pow_left₀ (by norm_num) exp_one_lower n
  rw [exp_neg]
  exact ((inv_le_inv₀ (exp_pos _) (by positivity)).mpr h).trans hB

theorem exp_minus_twelve_upper : exp (-12 : ℝ) ≤ 0.00000615 := by
  simpa only [Nat.cast_ofNat] using exp_negative_bound 12 (by norm_num :
    ((2.71828 : ℝ) ^ 12)⁻¹ ≤ 0.00000615)

theorem exp_minus_seventeen_upper : exp (-17 : ℝ) ≤ 0.0000000414 := by
  simpa only [Nat.cast_ofNat] using exp_negative_bound 17 (by norm_num :
    ((2.71828 : ℝ) ^ 17)⁻¹ ≤ 0.0000000414)

theorem exp_half_lower : (1.6487 : ℝ) ≤ exp (1 / 2) := by
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) 8
  have hn : (1.6487 : ℝ) ≤ ∑ i ∈ Finset.range 8, (1 / 2 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans h

end BstLean.Part253
