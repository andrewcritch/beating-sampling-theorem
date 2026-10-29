import BstLean.Part209Tail
import Mathlib.Algebra.Order.Ring.Pow

/-! Scalar factorial comparisons for the fixed-pair plane allowance. -/
namespace BstLean.Part209
open Real

noncomputable def factorialRoot (N : ℕ) : ℝ := (N.factorial : ℝ) ^ (1 / (N : ℝ))

lemma nat_root_pow {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c) :
    (c ^ (1 / (N : ℝ))) ^ N = c := by
  rw [← rpow_natCast, ← rpow_mul hc]
  have hn0 : (N : ℝ) ≠ 0 := by positivity
  rw [div_mul_cancel₀ _ hn0, rpow_one]

lemma factorialRoot_le {N : ℕ} (hN : 1 ≤ N) : factorialRoot N ≤ (N : ℝ) := by
  apply (pow_le_pow_iff_left₀ (by unfold factorialRoot; positivity) (by positivity)
    (show N ≠ 0 by omega)).mp
  rw [factorialRoot, nat_root_pow hN (by positivity)]
  exact_mod_cast Nat.factorial_le_pow N

lemma double_factorial_root_le {N : ℕ} (hN : 1 ≤ N) :
    (2 * (N.factorial : ℝ)) ^ (1 / (N : ℝ)) ≤ factorialRoot N + 1 := by
  have hn0 : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (2 : ℝ) ^ (1 / (N : ℝ)) ≤ 1 + 1 / (N : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (show N ≠ 0 by omega)).mp
    rw [nat_root_pow hN (by norm_num)]
    have h := one_add_mul_le_pow (a := 1 / (N : ℝ)) (by linarith [one_div_nonneg.mpr hn0.le]) N
    have he : (N : ℝ) * (1 / (N : ℝ)) = 1 := by field_simp
    simpa only [he, one_add_one_eq_two] using h
  rw [mul_rpow (by norm_num) (by positivity)]
  have hf0 : 0 ≤ factorialRoot N := by unfold factorialRoot; positivity
  have h := mul_le_mul_of_nonneg_right ht hf0
  have hf : factorialRoot N / (N : ℝ) ≤ 1 := (div_le_one hn0).mpr (factorialRoot_le hN)
  calc (2 : ℝ) ^ (1 / (N : ℝ)) * (N.factorial : ℝ) ^ (1 / (N : ℝ)) ≤
      (1 + 1 / (N : ℝ)) * factorialRoot N := h
    _ = factorialRoot N + factorialRoot N / (N : ℝ) := by ring
    _ ≤ factorialRoot N + 1 := add_le_add le_rfl hf

lemma one_le_log162 : 1 ≤ log (162 : ℝ) := by
  rw [← exp_le_exp, exp_log (by norm_num : (0 : ℝ) < 162)]
  linarith [exp_one_lt_d9]

lemma plane_gaussian_root_le {P : ℕ} (hP : 1 ≤ P) :
    (2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) ≤ sqrt (log 162 + factorialRoot P) := by
  have he : ((2 * (P.factorial : ℝ)) ^ (1 / (2 * (P : ℝ)))) ^ (2 : ℕ) =
      (2 * (P.factorial : ℝ)) ^ (1 / (P : ℝ)) := by
    rw [← rpow_natCast, ← rpow_mul (by positivity)]
    congr 1
    have hp0 : (P : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  apply le_sqrt_of_sq_le
  rw [he]
  have h := double_factorial_root_le hP
  linarith [one_le_log162]

noncomputable def pairPlane (n P : ℕ) : ℝ :=
  2 * sqrt 32 * (n : ℝ) * sqrt (log 162 + factorialRoot P) +
    8 * (log 162 + factorialRoot (2 * P))

/-- Two centered scalar-coordinate moments fit the paper plane constant. -/
theorem two_bernMoment_le_pairPlane {P : ℕ} (hP : 1 ≤ P) (n : ℕ) :
    2 * bernMoment (2 * sqrt 2 * (n : ℝ)) 2 2 P ≤ pairPlane n P := by
  have hg := plane_gaussian_root_le hP
  have he := double_factorial_root_le (show 1 ≤ 2 * P by omega)
  have hc : 1 / ((2 * P : ℕ) : ℝ) = 1 / (2 * (P : ℝ)) := by push_cast; rfl
  rw [hc] at he
  have ht : (2 * ((2 * P).factorial : ℝ)) ^ (1 / (2 * (P : ℝ))) ≤
      log 162 + factorialRoot (2 * P) := by linarith [one_le_log162]
  have hs : sqrt (32 : ℝ) = 4 * sqrt 2 := by
    rw [show (32 : ℝ) = 16 * 2 by norm_num, sqrt_mul (by norm_num)]
    norm_num
  unfold bernMoment pairPlane
  rw [hs]
  have h₁ := mul_le_mul_of_nonneg_left hg (show 0 ≤ 8 * sqrt 2 * (n : ℝ) by positivity)
  have h₂ := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 8)
  nlinarith

end BstLean.Part209
