import BstLean.Part247EBase

/-! Part 247: the second-layer Gram radius in the sharp E block. -/
namespace BstLean.Part247
open Real BstLean.Part130 BstLean.Part182 BstLean.Part244

theorem zeta_bound {n : ℕ} (hn : 11883 ≤ n) :
    √(2 / (mA n : ℝ)) * (√2 + √(2 * (n : ℝ)) + √(2 * 46)) ≤
      (19659 / 10 ^ 6 : ℝ) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn2 : (11883 : ℝ)^2 ≤ (n : ℝ)^2 := pow_le_pow_left₀ (by norm_num) hnR 2
  have h1 : √(2 / (mA n : ℝ)) * √2 ≤ (2 / 11883 : ℝ) := by
    apply en_sqrt_mul_le (by positivity) (by norm_num)
    rw [en_M, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : √(2 / (mA n : ℝ)) * √(2 * (n : ℝ)) ≤ (2 / 109 : ℝ) := by
    apply en_sqrt_mul_le (by positivity) (by norm_num)
    rw [en_M, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have h3 : √(2 / (mA n : ℝ)) * √(2 * 46) ≤ (135647 / 10000 / 11883 : ℝ) := by
    apply en_sqrt_mul_le (by positivity) (by norm_num)
    rw [en_M, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [mul_add, mul_add]
  linarith

theorem gram_radius_bound {n : ℕ} (hn : 11883 ≤ n) {k a R : ℝ}
    (hk : 0 ≤ k) (ha : 0 ≤ a) (hka : k ≤ a^2)
    (hR : 4 * a * (141422 / 100000 / 109 + 95917 / 10000 / 109^2) +
      8 / 109^4 + 2 * (141422 / 100000 / 109 + (95917 / 10000 + 2) / 109^2)^2 ≤ R) :
    2 / (mA n : ℝ) *
      (2 * √((mA n : ℝ) * k) * (√(2 * (n : ℝ)) + √(2 * 46)) + 4 +
        (√(2 * (n : ℝ)) + √(2 * 46) + 2)^2) ≤ R := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hn0
  have hr2 : r^2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hrlo : (109 : ℝ) ≤ r := Real.le_sqrt_of_sq_le (by nlinarith)
  set u := 1 / r with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ (1 / 109 : ℝ) := one_div_le_one_div_of_le (by norm_num) hrlo
  have hsm : √(mA n : ℝ) = n := by rw [en_M, Real.sqrt_sq hn0.le]
  have hK : √((mA n : ℝ) * k) = n * √k := by
    rw [Real.sqrt_mul (by positivity), hsm]
  have h2n : √(2 * (n : ℝ)) = √2 * r := Real.sqrt_mul (by norm_num) _
  have hs : √k ≤ a := (Real.sqrt_le_left ha).mpr hka
  have hs0 : 0 ≤ √k := Real.sqrt_nonneg _
  have ht : √(2 : ℝ) ≤ 141422 / 100000 := en_sq_le (by norm_num) (by norm_num)
  have hv : √(2 * (46 : ℝ)) ≤ 95917 / 10000 := en_sq_le (by norm_num) (by norm_num)
  rw [hK, h2n, en_M]
  have hid : 2 / (n : ℝ)^2 *
      (2 * ((n : ℝ) * √k) * (√2 * r + √(2 * 46)) + 4 +
        (√2 * r + √(2 * 46) + 2)^2) =
      4 * √k * (√2 * u + √(2 * 46) * u^2) + 8 * u^4 +
        2 * (√2 * u + (√(2 * 46) + 2) * u^2)^2 := by
    rw [hu, ← hr2]
    field_simp
    <;> ring
  rw [hid]
  refine le_trans ?_ hR
  have hbound :
      4 * √k * (√2 * u + √(2 * 46) * u^2) + 8 * u^4 +
        2 * (√2 * u + (√(2 * 46) + 2) * u^2)^2 ≤
      4 * a * (141422 / 100000 * (1 / 109) + 95917 / 10000 * (1 / 109)^2) +
        8 * (1 / 109)^4 +
        2 * (141422 / 100000 * (1 / 109) + (95917 / 10000 + 2) * (1 / 109)^2)^2 := by
    gcongr
  convert hbound using 1 <;> ring

end BstLean.Part247
