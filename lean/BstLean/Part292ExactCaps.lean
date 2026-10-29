import BstLean.Part292Counts

/-! One monotone bound for every row count at least 64000000. -/
namespace BstLean.Part292
open Real BstLean.Part239

theorem geometric_polynomial_bound (a : ℕ → ℝ) (d : ℕ) {x B : ℝ}
    (ha : ∀ k, 0 ≤ a k) (hx : 0 ≤ x) (hBx : B ≤ x)
    (hstep : ∀ k, k < d → 2 * a k ≤ B * a (k+1)) :
    ∑ k ∈ Finset.range (d+1), a k * x^k ≤ 2 * a d * x^d := by
  induction d with
  | zero => simp only [Nat.zero_add, Finset.sum_range_one, pow_zero, mul_one]; nlinarith [ha 0]
  | succ d ih =>
    rw [Finset.sum_range_succ]
    have h := ih (fun k hk => hstep k (by omega))
    have hnext : 2 * a d ≤ x * a (d+1) :=
      (hstep d (by omega)).trans (mul_le_mul_of_nonneg_right hBx (ha _))
    have hmul := mul_le_mul_of_nonneg_right hnext (pow_nonneg hx d)
    rw [pow_succ]
    nlinarith

theorem count_ratio_52 (k : ℕ) (hk : k < 26) :
    2 * (noSingleton 52 k : ℝ) ≤ 64000000 * (noSingleton 52 (k+1) : ℝ) := by
  interval_cases k
  · norm_num only [count_52_0, count_52_1, Nat.cast_ofNat]
  · norm_num only [count_52_1, count_52_2, Nat.cast_ofNat]
  · norm_num only [count_52_2, count_52_3, Nat.cast_ofNat]
  · norm_num only [count_52_3, count_52_4, Nat.cast_ofNat]
  · norm_num only [count_52_4, count_52_5, Nat.cast_ofNat]
  · norm_num only [count_52_5, count_52_6, Nat.cast_ofNat]
  · norm_num only [count_52_6, count_52_7, Nat.cast_ofNat]
  · norm_num only [count_52_7, count_52_8, Nat.cast_ofNat]
  · norm_num only [count_52_8, count_52_9, Nat.cast_ofNat]
  · norm_num only [count_52_9, count_52_10, Nat.cast_ofNat]
  · norm_num only [count_52_10, count_52_11, Nat.cast_ofNat]
  · norm_num only [count_52_11, count_52_12, Nat.cast_ofNat]
  · norm_num only [count_52_12, count_52_13, Nat.cast_ofNat]
  · norm_num only [count_52_13, count_52_14, Nat.cast_ofNat]
  · norm_num only [count_52_14, count_52_15, Nat.cast_ofNat]
  · norm_num only [count_52_15, count_52_16, Nat.cast_ofNat]
  · norm_num only [count_52_16, count_52_17, Nat.cast_ofNat]
  · norm_num only [count_52_17, count_52_18, Nat.cast_ofNat]
  · norm_num only [count_52_18, count_52_19, Nat.cast_ofNat]
  · norm_num only [count_52_19, count_52_20, Nat.cast_ofNat]
  · norm_num only [count_52_20, count_52_21, Nat.cast_ofNat]
  · norm_num only [count_52_21, count_52_22, Nat.cast_ofNat]
  · norm_num only [count_52_22, count_52_23, Nat.cast_ofNat]
  · norm_num only [count_52_23, count_52_24, Nat.cast_ofNat]
  · norm_num only [count_52_24, count_52_25, Nat.cast_ofNat]
  · norm_num only [count_52_25, count_52_26, Nat.cast_ofNat]

theorem exact_partition_cap_52 (m : ℕ) (hm : 64000000 ≤ m) :
    partitionPolynomial 52 m ≤ (9/2 : ℝ)^52 * (m : ℝ)^26 := by
  rw [partitionPolynomial_half_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (26+1), (noSingleton 52 k : ℝ) * (m : ℝ)^k := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.descFactorial_le_pow m k
    _ ≤ 2 * (noSingleton 52 26 : ℝ) * (m : ℝ)^26 :=
      geometric_polynomial_bound _ _ (fun k => Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (by exact_mod_cast hm) (count_ratio_52)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
      norm_num only [count_52_26, Nat.cast_ofNat]
theorem count_ratio_104 (k : ℕ) (hk : k < 52) :
    2 * (noSingleton 104 k : ℝ) ≤ 64000000 * (noSingleton 104 (k+1) : ℝ) := by
  interval_cases k
  · norm_num only [count_104_0, count_104_1, Nat.cast_ofNat]
  · norm_num only [count_104_1, count_104_2, Nat.cast_ofNat]
  · norm_num only [count_104_2, count_104_3, Nat.cast_ofNat]
  · norm_num only [count_104_3, count_104_4, Nat.cast_ofNat]
  · norm_num only [count_104_4, count_104_5, Nat.cast_ofNat]
  · norm_num only [count_104_5, count_104_6, Nat.cast_ofNat]
  · norm_num only [count_104_6, count_104_7, Nat.cast_ofNat]
  · norm_num only [count_104_7, count_104_8, Nat.cast_ofNat]
  · norm_num only [count_104_8, count_104_9, Nat.cast_ofNat]
  · norm_num only [count_104_9, count_104_10, Nat.cast_ofNat]
  · norm_num only [count_104_10, count_104_11, Nat.cast_ofNat]
  · norm_num only [count_104_11, count_104_12, Nat.cast_ofNat]
  · norm_num only [count_104_12, count_104_13, Nat.cast_ofNat]
  · norm_num only [count_104_13, count_104_14, Nat.cast_ofNat]
  · norm_num only [count_104_14, count_104_15, Nat.cast_ofNat]
  · norm_num only [count_104_15, count_104_16, Nat.cast_ofNat]
  · norm_num only [count_104_16, count_104_17, Nat.cast_ofNat]
  · norm_num only [count_104_17, count_104_18, Nat.cast_ofNat]
  · norm_num only [count_104_18, count_104_19, Nat.cast_ofNat]
  · norm_num only [count_104_19, count_104_20, Nat.cast_ofNat]
  · norm_num only [count_104_20, count_104_21, Nat.cast_ofNat]
  · norm_num only [count_104_21, count_104_22, Nat.cast_ofNat]
  · norm_num only [count_104_22, count_104_23, Nat.cast_ofNat]
  · norm_num only [count_104_23, count_104_24, Nat.cast_ofNat]
  · norm_num only [count_104_24, count_104_25, Nat.cast_ofNat]
  · norm_num only [count_104_25, count_104_26, Nat.cast_ofNat]
  · norm_num only [count_104_26, count_104_27, Nat.cast_ofNat]
  · norm_num only [count_104_27, count_104_28, Nat.cast_ofNat]
  · norm_num only [count_104_28, count_104_29, Nat.cast_ofNat]
  · norm_num only [count_104_29, count_104_30, Nat.cast_ofNat]
  · norm_num only [count_104_30, count_104_31, Nat.cast_ofNat]
  · norm_num only [count_104_31, count_104_32, Nat.cast_ofNat]
  · norm_num only [count_104_32, count_104_33, Nat.cast_ofNat]
  · norm_num only [count_104_33, count_104_34, Nat.cast_ofNat]
  · norm_num only [count_104_34, count_104_35, Nat.cast_ofNat]
  · norm_num only [count_104_35, count_104_36, Nat.cast_ofNat]
  · norm_num only [count_104_36, count_104_37, Nat.cast_ofNat]
  · norm_num only [count_104_37, count_104_38, Nat.cast_ofNat]
  · norm_num only [count_104_38, count_104_39, Nat.cast_ofNat]
  · norm_num only [count_104_39, count_104_40, Nat.cast_ofNat]
  · norm_num only [count_104_40, count_104_41, Nat.cast_ofNat]
  · norm_num only [count_104_41, count_104_42, Nat.cast_ofNat]
  · norm_num only [count_104_42, count_104_43, Nat.cast_ofNat]
  · norm_num only [count_104_43, count_104_44, Nat.cast_ofNat]
  · norm_num only [count_104_44, count_104_45, Nat.cast_ofNat]
  · norm_num only [count_104_45, count_104_46, Nat.cast_ofNat]
  · norm_num only [count_104_46, count_104_47, Nat.cast_ofNat]
  · norm_num only [count_104_47, count_104_48, Nat.cast_ofNat]
  · norm_num only [count_104_48, count_104_49, Nat.cast_ofNat]
  · norm_num only [count_104_49, count_104_50, Nat.cast_ofNat]
  · norm_num only [count_104_50, count_104_51, Nat.cast_ofNat]
  · norm_num only [count_104_51, count_104_52, Nat.cast_ofNat]

theorem exact_partition_cap_104 (m : ℕ) (hm : 64000000 ≤ m) :
    partitionPolynomial 104 m ≤ (63/10 : ℝ)^104 * (m : ℝ)^52 := by
  rw [partitionPolynomial_half_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (52+1), (noSingleton 104 k : ℝ) * (m : ℝ)^k := by
      apply Finset.sum_le_sum
      intro k _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.descFactorial_le_pow m k
    _ ≤ 2 * (noSingleton 104 52 : ℝ) * (m : ℝ)^52 :=
      geometric_polynomial_bound _ _ (fun k => Nat.cast_nonneg _)
        (Nat.cast_nonneg _) (by exact_mod_cast hm) (count_ratio_104)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg _) _)
      norm_num only [count_104_52, Nat.cast_ofNat]

end BstLean.Part292
