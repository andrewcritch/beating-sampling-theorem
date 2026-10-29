import BstLean.Part245Bounds

namespace BstLean.Part247
open Real Set BstLean.Part130 BstLean.Part182

noncomputable def eta : ℝ := 405 / 1000000

theorem ko_bound {n : ℕ} (hn : 11883 ≤ n) :
    o3_kO n 46 (((mA n : ℕ) : ℝ) * (1 / 2 + eta)) (((mA n : ℕ) : ℝ) * (1 / 2 + eta)) ≤
      (n : ℝ) * (35 / 1000) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hn0
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr1 : (1090 / 10 : ℝ) ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hsm : √(((mA n : ℕ) : ℝ)) = n := by rw [hm, Real.sqrt_sq hn0.le]
  set s := √(1 / 2 + eta) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 70740 / 100000 := sn_sqrt_le (by norm_num) (by rw [eta]; norm_num)
  have hK : √(((mA n : ℕ) : ℝ) * (1 / 2 + eta)) = n * s := by
    rw [Real.sqrt_mul (by positivity), hsm]
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := sn_sqrt_le (by norm_num) (by norm_num)
  set t3 := √(3 : ℝ) with ht3
  have ht30 : 0 ≤ t3 := Real.sqrt_nonneg _
  have ht31 : t3 ≤ 17321 / 10000 := sn_sqrt_le (by norm_num) (by norm_num)
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hg : √(2 / (n : ℝ)) = √2 / r := by rw [Real.sqrt_div (by norm_num)]
  have hgm : √(2 / ((mA n : ℕ) : ℝ)) = √2 / n := by
    rw [Real.sqrt_div (by norm_num), hsm]
  unfold o3_kO
  rw [hK, hg, hgm, hsm, ← hv]
  set u := 1 / r with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u ≤ 10 / 1090 := by
    rw [hu, div_le_div_iff₀ hr0 (by norm_num)]; linarith
  have hnr : (n : ℝ) = 1 / u ^ 2 := by rw [hu, ← hrr]; field_simp
  have hru : r = 1 / u := by rw [hu]; field_simp
  
  have key : (√2 / r * (r + v)) * (√2 / n * ((n + t3 + v) + (n * s + v))) *
      (√2 / r * v * (√2 / n * (n + v)) + √2 / n * (n * s + v) * (√2 / r * (n * s + v))) =
      (n : ℝ) * (4 * (1 + v * u) * ((1 + s) + (t3 + 2 * v) * u ^ 2) *
        (v * u ^ 3 * (1 + v * u ^ 2) + u * (s + v * u ^ 2) ^ 2)) := by
    have hu' : u ≠ 0 := by positivity
    rw [hnr, hru]
    have h4 : √(2 : ℝ) ^ 4 = 4 := by rw [show √(2 : ℝ) ^ 4 = (√2 ^ 2) ^ 2 by ring, h2]; norm_num
    field_simp
    rw [h4]
    ring
  rw [key]
  refine mul_le_mul_of_nonneg_left ?_ hn0.le
  have e1 : 1 + v * u ≤ 1 + 95917 / 10000 * (10 / 1090) := by gcongr
  have e2 : (1 + s) + (t3 + 2 * v) * u ^ 2 ≤
      (1 + 70740 / 100000) + (17321 / 10000 + 2 * (95917 / 10000)) * (10 / 1090) ^ 2 := by gcongr
  have e3 : v * u ^ 3 * (1 + v * u ^ 2) + u * (s + v * u ^ 2) ^ 2 ≤
      95917 / 10000 * (10 / 1090) ^ 3 * (1 + 95917 / 10000 * (10 / 1090) ^ 2) +
        10 / 1090 * (70740 / 100000 + 95917 / 10000 * (10 / 1090) ^ 2) ^ 2 := by gcongr
  calc 4 * (1 + v * u) * ((1 + s) + (t3 + 2 * v) * u ^ 2) *
        (v * u ^ 3 * (1 + v * u ^ 2) + u * (s + v * u ^ 2) ^ 2)
      ≤ 4 * (1 + 95917 / 10000 * (10 / 1090)) *
          ((1 + 70740 / 100000) + (17321 / 10000 + 2 * (95917 / 10000)) * (10 / 1090) ^ 2) *
          (95917 / 10000 * (10 / 1090) ^ 3 * (1 + 95917 / 10000 * (10 / 1090) ^ 2) +
            10 / 1090 * (70740 / 100000 + 95917 / 10000 * (10 / 1090) ^ 2) ^ 2) := by
        gcongr
    _ ≤ 35 / 1000 := by norm_num

lemma inv_le {x a k : ℝ} (hx : 11883 ≤ x) (ha : 0 ≤ a) (hk : a ≤ k * 11883 * 11883) :
    a / x ≤ k * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hk0 : 0 ≤ k := by nlinarith
  rw [div_le_iff₀ hx0]
  have : k * 11883 * 11883 ≤ k * x * x := by
    have h1 : (11883 : ℝ) * 11883 ≤ x * x := mul_le_mul hx hx (by norm_num) hx0.le
    nlinarith
  linarith

lemma rs_le {n : ℕ} (hn : 11883 ≤ n) : s3rs n 46 eta ≤ n * (3400 / 10 ^ 6) := by
  have hnR : (11883 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hsm : √(((mA n : ℕ) : ℝ)) = n := by rw [hm, Real.sqrt_sq hn0.le]
  set s := √(1 / 2 + eta) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : s ≤ 70740 / 100000 := sn_sqrt_le (by norm_num) (by rw [eta]; norm_num)
  have hK : √(s3K n eta) = n * s := by
    unfold s3K; rw [Real.sqrt_mul (by positivity), hsm]
  set v := √(2 * (46 : ℝ)) with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hv1 : v ≤ 95917 / 10000 := sn_sqrt_le (by norm_num) (by norm_num)
  have hsq2 : √(2 * ((mA n : ℕ) : ℝ) * 46) = n * v := by
    rw [hm, show 2 * (n : ℝ) ^ 2 * 46 = (n : ℝ) ^ 2 * (2 * 46) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  have hpp : s3pp n 46 eta ^ 2 = 2 / n * (n * s + v) ^ 2 := by
    unfold s3pp; rw [hK, ← hv, mul_pow, Real.sq_sqrt (by positivity)]
  have hrs : s3rs n 46 eta = 8 * (n * s + v) ^ 2 * (n * v + 46) / (n : ℝ) ^ 3 := by
    unfold s3rs; rw [hpp, hsq2, hm]; field_simp; ring
  rw [hrs, div_le_iff₀ (by positivity)]
  have hA : n * s + v ≤ n * (70821 / 100000) := by
    have : v ≤ n * (81 / 100000) := by nlinarith
    nlinarith
  have hB : n * v + 46 ≤ n * (95957 / 10000) := by
    have : (46 : ℝ) ≤ n * (40 / 10000) := by nlinarith
    nlinarith
  have hA0 : 0 ≤ n * s + v := by positivity
  have h1 : (n * s + v) ^ 2 ≤ (n * (70821 / 100000)) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have h2 : (n * s + v) ^ 2 * (n * v + 46) ≤ (n * (70821 / 100000)) ^ 2 * (n * (95957 / 10000)) :=
    mul_le_mul h1 hB (by positivity) (by positivity)
  have h3 : 8 * ((n * (70821 / 100000)) ^ 2 * (n * (95957 / 10000))) ≤
      n * (3400 / 10 ^ 6) * (n : ℝ) ^ 3 := by
    have e : 8 * ((n * (70821 / 100000)) ^ 2 * (n * (95957 / 10000))) =
        (8 * (70821 / 100000) ^ 2 * (95957 / 10000)) * (n : ℝ) ^ 3 := by ring
    rw [e]
    have hn3 : 0 ≤ (n : ℝ) ^ 3 := by positivity
    have : (8 * (70821 / 100000) ^ 2 * (95957 / 10000) : ℝ) ≤ n * (3400 / 10 ^ 6) := by
      norm_num; linarith
    exact mul_le_mul_of_nonneg_right this hn3
  linarith


end BstLean.Part247
