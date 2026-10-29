import BstLean.Part207Moments

/-! The paper's HQ price and its coefficient transfer. -/
namespace BstLean.Part207
open Real

/-- `Y` includes the squared normalized centre norm. -/
noncomputable def hqL (n : ℕ) (e X Y : ℝ) : ℝ :=
  n * X / (4 * (1 - e) ^ 2) + Y / (2 * (1 - e)) +
    (√(X * Y) + √((n : ℝ) / 2) * X) / (1 - e)

lemma hqL_nonneg {n : ℕ} {e X Y : ℝ} (he : e < 1) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ hqL n e X Y := by
  have hd : 0 < 1 - e := by linarith
  unfold hqL
  positivity

/-- Transfer the three Jensen coefficients to the exact price in HQ. -/
theorem triangle_le_hqL {n : ℕ} {e X Y K b c a : ℝ}
    (he : e < 1) (hX : 0 ≤ X) (hY : 0 ≤ Y) (ha : 0 ≤ a)
    (hK : |K| ≤ n * (1 / (4 * (1 - e) ^ 2)) * X + Y / (2 * (1 - e)))
    (hb : b ^ 2 ≤ X ^ 2 / (1 - e) ^ 2)
    (hc : a * c ^ 2 ≤ Y * X / (1 - e) ^ 2) :
    |K| + |b / 2| * √(2 * (n : ℝ)) + √(a * c ^ 2) ≤ hqL n e X Y := by
  have hd : 0 < 1 - e := by linarith
  have hb' : |b| ≤ X / (1 - e) := by
    have hs : |b| ^ 2 ≤ (X / (1 - e)) ^ 2 := by simpa [div_pow] using hb
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp hs
  have hc' : √(a * c ^ 2) ≤ √(X * Y) / (1 - e) := by
    have hs := Real.sqrt_le_sqrt hc
    rw [Real.sqrt_div (mul_nonneg hY hX), Real.sqrt_sq hd.le, mul_comm Y X] at hs
    exact hs
  have heq : √(2 * (n : ℝ)) / 2 = √((n : ℝ) / 2) := by
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * n by positivity)
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) / 2 by positivity)
    nlinarith [Real.sqrt_nonneg (2 * (n : ℝ)), Real.sqrt_nonneg ((n : ℝ) / 2)]
  have hb'' : |b / 2| * √(2 * (n : ℝ)) ≤ √((n : ℝ) / 2) * X / (1 - e) := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc |b| / 2 * √(2 * (n : ℝ)) = |b| * (√(2 * (n : ℝ)) / 2) := by ring
      _ = |b| * √((n : ℝ) / 2) := by rw [heq]
      _ ≤ (X / (1 - e)) * √((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hb' (Real.sqrt_nonneg _)
      _ = _ := by ring
  unfold hqL
  calc _ ≤ n * (1 / (4 * (1 - e) ^ 2)) * X + Y / (2 * (1 - e)) +
      √((n : ℝ) / 2) * X / (1 - e) + √(X * Y) / (1 - e) := by linarith
    _ = _ := by ring

end BstLean.Part207
