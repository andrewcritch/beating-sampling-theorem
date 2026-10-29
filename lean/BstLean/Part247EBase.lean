import BstLean.Part247SBase
import BstLean.Part244TI

/-! Part 247: uniform first-layer envelopes for the sharp E block. -/
namespace BstLean.Part247
open Real BstLean.Part130 BstLean.Part182 BstLean.Part244
variable {n : ℕ}

lemma eb_bound (hn : 11883 ≤ n) {k a : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) (hka : 2 * k ≤ a ^ 2) :
    e4_b n (((mA n : ℕ) : ℝ) * k) 46 ≤
      √(n : ℝ) * (a + 141422 / 100000 * (10 / 1090) + 135647 / 10000 * (10 / 1090) ^ 2) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := en_M n
  set r := √(n : ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrlo : 1090 / 10 ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hr0' : 0 < r := by linarith
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := en_sq_le (by norm_num) (by norm_num)
  have h184 : √(184 : ℝ) ≤ 135647 / 10000 := en_sq_le (by norm_num) (by norm_num)
  have hrv : 1 ≤ r * (10 / 1090) := by linarith
  unfold e4_b
  rw [mul_add, mul_add, mul_add, mul_add]
  have x1 : √(2 / (n : ℝ)) * √(((mA n : ℕ) : ℝ) * k) ≤ r * a := by
    refine en_sqrt_mul_le (by positivity) (by positivity) ?_
    rw [hM, mul_pow, hrr]
    have e : 2 / (n : ℝ) * ((n : ℝ) ^ 2 * k) = n * (2 * k) := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left hka hn0.le
  have x2 : √(2 / (n : ℝ)) * √(n : ℝ) ≤ r * (141422 / 100000 * (10 / 1090)) := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * n = 2 := by field_simp
    rw [e]
    have : 141422 / 100000 * 1 ≤ 141422 / 100000 * (r * (10 / 1090)) :=
      mul_le_mul_of_nonneg_left hrv (by norm_num)
    nlinarith
  have x3 : √(2 / (n : ℝ)) * √(2 * 46) ≤ r * (135647 / 10000 * (10 / 1090) ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * (2 * 46) = 184 / r ^ 2 := by rw [hrr]; ring
    rw [e, Real.sqrt_div (by norm_num), Real.sqrt_sq hr0, div_le_iff₀ hr0']
    have h1 : 1 ≤ (r * (10 / 1090)) ^ 2 := by nlinarith
    have : 135647 / 10000 * 1 ≤ 135647 / 10000 * (r * (10 / 1090)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    nlinarith
  linarith


lemma pi_bound (hn : 11883 ≤ n) :
    e4_b n 2 46 ≤ 20 / 1090 + 141422 / 100000 + 135647 / 10000 * (10 / 1090) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := en_sq_le (by norm_num) (by norm_num)
  unfold e4_b
  rw [mul_add, mul_add]
  have x1 : √(2 / (n : ℝ)) * √2 ≤ 20 / 1090 := by
    refine en_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]; nlinarith
  have x2 : √(2 / (n : ℝ)) * √(n : ℝ) ≤ 141422 / 100000 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * n = 2 := by field_simp
    rw [e]; exact h2
  have x3 : √(2 / (n : ℝ)) * √(2 * 46) ≤ 135647 / 10000 * (10 / 1090) := by
    refine en_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]; nlinarith
  linarith


lemma tauf_bound (hn : 11883 ≤ n) :
    √(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + √(2 * 46)) ≤
      141422 / 100000 + 2 / 11883 + 135647 / 10000 / 11883 := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := en_M n
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [hM]; positivity
  have hsq : (11883 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := en_sq_le (by norm_num) (by norm_num)
  rw [mul_add, mul_add]
  have x1 : √(2 / ((mA n : ℕ) : ℝ)) * √((mA n : ℕ) : ℝ) ≤ 141422 / 100000 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / ((mA n : ℕ) : ℝ) * ((mA n : ℕ) : ℝ) = 2 := by field_simp
    rw [e]; exact h2
  have x2 : √(2 / ((mA n : ℕ) : ℝ)) * √2 ≤ 2 / 11883 := by
    refine en_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have x3 : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * 46) ≤ 135647 / 10000 / 11883 := by
    refine en_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


end BstLean.Part247
