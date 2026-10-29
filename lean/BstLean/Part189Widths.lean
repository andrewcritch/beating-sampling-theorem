import BstLean.Part130Extra
namespace BstLean.Part189
open BstLean.Part130
noncomputable section

lemma half_power (n e : ℕ) :
    (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) / 2) = (n : ℝ) ^ e * Real.sqrt n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  apply (sq_eq_sq₀ (Real.rpow_nonneg hn _) (by positivity)).mp
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num only [Nat.cast_ofNat]
  have h : (((2 * e + 1 : ℕ) : ℝ) / 2) * (2 : ℝ) = (2 * e + 1 : ℕ) := by ring
  rw [h, Real.rpow_natCast, mul_pow, Real.sq_sqrt hn]
  push_cast
  ring

lemma widthF_le (n : ℕ) : (mF n : ℝ) ≤ (n : ℝ) * Real.sqrt n + 1 := by
  unfold mF
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) ((3 : ℝ) / 2))
  have hpow := half_power n 1
  norm_num at hpow
  rw [hpow] at h ⊢
  exact h.le

lemma widthW_le (n : ℕ) : (mW n : ℝ) ≤ (n : ℝ) ^ 3 * Real.sqrt n + 1 := by
  unfold mW
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg n) ((7 : ℝ) / 2))
  have hpow := half_power n 3
  norm_num at hpow
  rw [hpow] at h ⊢
  exact h.le

end
end BstLean.Part189
