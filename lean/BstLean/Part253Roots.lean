import BstLean.Part219Direction
import Mathlib.Analysis.Real.Pi.Bounds

/-! Scalar root and logarithm certificates for the direction formula. -/
namespace BstLean.Part253
open Real

theorem root_upper {x b : ℝ} {k : ℕ} (hk : k ≠ 0) (hx : 0 ≤ x)
    (hb : 0 ≤ b) (h : x ≤ b ^ k) : x ^ ((k : ℝ)⁻¹) ≤ b := by
  apply le_of_pow_le_pow_left₀ hk hb
  rw [rpow_inv_natCast_pow hx hk]
  exact h

theorem log162_upper : log (162 : ℝ) ≤ 5.088 := by
  apply (log_le_iff_le_exp (by norm_num : (0 : ℝ) < 162)).mpr
  have h := sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 5.088) 24
  have hn : (162 : ℝ) ≤ ∑ i ∈ Finset.range 24, (5.088 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hn.trans h

theorem exp_minus_one_half : exp (-1 : ℝ) ≤ 1 / 2 := by
  rw [exp_neg]
  rw [one_div]
  exact (inv_le_inv₀ (exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr
    (by linarith [add_one_le_exp (1 : ℝ)])

theorem low_length_root : BstLean.Part209.lowLengthProb 12225 (1 / 100) ^ (1 / 128 : ℝ) ≤
    (1 / 1000000 : ℝ) := by
  have hp : 0 ≤ BstLean.Part209.lowLengthProb 12225 (1 / 100) := by
    unfold BstLean.Part209.lowLengthProb
    positivity
  have hexp : exp (-(12225 : ℝ) ^ 2 * (1 / 100 - 2 / (12225 : ℝ) ^ 2) ^ 2 / 4) ≤
      (1 / 2 : ℝ) ^ 3072 := by
    calc
      _ ≤ exp (3072 * (-1 : ℝ)) := exp_le_exp.mpr (by norm_num)
      _ = exp (-1 : ℝ) ^ 3072 := by simpa using exp_nat_mul (-1 : ℝ) 3072
      _ ≤ _ := pow_le_pow_left₀ (exp_pos _).le exp_minus_one_half _
  have hpow : BstLean.Part209.lowLengthProb 12225 (1 / 100) ≤
      (1 / 1000000 : ℝ) ^ 128 := by
    unfold BstLean.Part209.lowLengthProb
    calc
      _ ≤ 4 * (1 / 2 : ℝ) ^ 3072 := mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 4 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by rw [← pow_mul]
      _ ≤ (2 : ℝ) ^ 128 * ((1 / 2 : ℝ) ^ 24) ^ 128 := by
        gcongr
        norm_num
      _ = ((2 : ℝ) * (1 / 2) ^ 24) ^ 128 := by rw [mul_pow]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by norm_num) _
  have h := root_upper (by norm_num : (128 : ℕ) ≠ 0) hp (by norm_num) hpow
  norm_num only [Nat.cast_ofNat] at h
  exact h

end BstLean.Part253
