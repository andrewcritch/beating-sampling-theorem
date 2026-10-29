import BstLean.Part185D7
import BstLean.Part184ISNum
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part 185 (file `D5`): numerics of the two-sided E block at `τ = 46`, `n ≥ 16 384`

No proof is left open; no `native_decide` or `axiom` is used. Rational constants were chosen with a
single-process python calculator; Lean checks every inequality.

* `t5_geom`: `a₊² ≤ n + 27.141`, `a₋² ≥ n − 27.130`, `d₋² ≥ 2n(1 − κ) − 76.735`,
  `d₊² ≤ 2n(1 − κ) + 76.778` (`τ = 46`, `n ≥ 16 384`).
* `t5_c1_le`, `t5_c1lo_ge`: `c₁⁺ ≤ C₁` and `c₁⁻ ≥ C₁⁻` from bounds on `κ(c)`.
* `t5_net`: `(2⌈√(2n)/ε⌉ + 1)^{2n} e^{−K_lo δ²/4} ≤ 2·10⁻¹⁹` for `ε = 1/100`, `δ = 1/8`,
  `K_lo ≥ 0.336m`.
* `t5_final2`: the final arithmetic of the two-sided bound.
* **`t5_cell`**: the E-block conditions of `d4_num` on one cell `[c_a, c_b]` of the window.
-/

namespace BstLean.Part186.T

open BstLean.Part185

open BstLean.Part182
open BstLean.Part184.IT (fsn_kdot_le fsn_kdot_ge fsn_kappa_le fsn_arcsin_ge fsn_kappa_eq
  fsn_pi_lo fsn_pi_hi)
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130
open BstLean.Part184 (gridN)

variable {n : ℕ}

lemma t5_M (n : ℕ) : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring

lemma t5_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : √a ≤ b :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hb))

/-- **The geometric bounds at `τ = 46`, `n ≥ 16 384`.** -/
theorem t5_geom (hn : 16384 ≤ n) {c : ℝ} (hκ0 : 0 ≤ kappa c) (hκ1 : kappa c ≤ 3 / 4) :
    0 < s3am n 46 ∧ s3ap n 46 ^ 2 ≤ n + 27141 / 1000 ∧ (n : ℝ) - 27130 / 1000 ≤ s3am n 46 ^ 2 ∧
      s3am n 46 ^ 2 ≤ s3ap n 46 ^ 2 ∧
      0 ≤ s3dm n 46 c ∧ 2 * n * (1 - kappa c) - 76735 / 1000 ≤ s3dm n 46 c ^ 2 ∧
      s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧
      (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
        2 * n * (1 - kappa c) + 76782 / 1000 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  set q := √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) with hq
  have hq0 : 0 ≤ q := by positivity
  have hqq : q ^ 2 = 184 / n := by
    rw [hq, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by positivity)]; ring
  have hqr : q * r = √(2 * (46 : ℝ)) * √2 := by
    rw [hq, hr, mul_assoc, ← Real.sqrt_mul (by positivity)]
    congr 2
    field_simp
  have h92 : √(2 * (46 : ℝ)) ≤ 959167 / 100000 := t5_sq_le (by norm_num) (by norm_num)
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := t5_sq_le (by norm_num) (by norm_num)
  have hqrb : q * r ≤ 959167 / 100000 * (141422 / 100000) := by
    rw [hqr]; exact mul_le_mul h92 h2 (Real.sqrt_nonneg _) (by norm_num)
  have hq2 : q ^ 2 ≤ 184 / 16384 := by
    rw [hqq]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have hap : s3ap n 46 = r + q := rfl
  set s := √((n : ℝ) - 2 / n) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have h2n : 2 / (n : ℝ) ≤ 2 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have h2n0 : 0 ≤ 2 / (n : ℝ) := by positivity
  have hn2 : 0 ≤ (n : ℝ) - 2 / n := by linarith
  have hss : s ^ 2 = (n : ℝ) - 2 / n := Real.sq_sqrt hn2
  have hsr : s ≤ r := Real.sqrt_le_sqrt (by linarith)
  have ham : s3am n 46 = s - q := rfl
  have hsq : q < s := by
    have h1 : q ^ 2 < s ^ 2 := by
      rw [hqq, hss]
      have : 186 / (n : ℝ) ≤ 186 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
      have e : 184 / (n : ℝ) + 2 / n = 186 / n := by ring
      linarith
    exact (pow_lt_pow_iff_left₀ hq0 hs0 two_ne_zero).1 h1
  have hamp : 0 < s3am n 46 := by rw [ham]; linarith
  have hqr0 : 0 ≤ q * r := mul_nonneg hq0 hr0
  have hap2 : s3ap n 46 ^ 2 ≤ n + 27141 / 1000 := by
    rw [hap]
    have e : (r + q) ^ 2 = r ^ 2 + 2 * (q * r) + q ^ 2 := by ring
    rw [e, hrr]; linarith
  have ham2 : (n : ℝ) - 27130 / 1000 ≤ s3am n 46 ^ 2 := by
    rw [ham]
    have h1 : s * q ≤ r * q := mul_le_mul_of_nonneg_right hsr hq0
    have e : (s - q) ^ 2 = s ^ 2 - 2 * (s * q) + q ^ 2 := by ring
    have e2 : r * q = q * r := by ring
    have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
    rw [e, hss]; linarith
  have hamap : s3am n 46 ^ 2 ≤ s3ap n 46 ^ 2 := by
    rw [ham, hap]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2
  -- `d₋`
  set X := √(2 * n * (1 - kappa c) - 4 * (2 / n)) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have h1κ : (1 : ℝ) / 4 ≤ 1 - kappa c := by linarith
  have e8 : 4 * (2 / (n : ℝ)) = 8 / n := by ring
  have h8n : 8 / (n : ℝ) ≤ 8 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have h8n0 : 0 ≤ 8 / (n : ℝ) := by positivity
  have h2nκ : 2 * 16384 * (1 / 4 : ℝ) ≤ 2 * n * (1 - kappa c) := by
    have := mul_le_mul hnR h1κ (by norm_num) hn0.le
    linarith
  have harg : 0 ≤ 2 * n * (1 - kappa c) - 4 * (2 / (n : ℝ)) := by rw [e8]; linarith
  have hXX : X ^ 2 = 2 * n * (1 - kappa c) - 4 * (2 / n) := Real.sq_sqrt harg
  have hdm : s3dm n 46 c = X - 2 * q := rfl
  have hX2q : 2 * q ≤ X := by
    have h1 : (2 * q) ^ 2 ≤ X ^ 2 := by
      have e : (2 * q) ^ 2 = 736 / n := by rw [mul_pow, hqq]; ring
      have : 736 / (n : ℝ) ≤ 736 / 16384 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
      rw [e, hXX, e8]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hX0 two_ne_zero).1 h1
  have hdm0 : 0 ≤ s3dm n 46 c := by rw [hdm]; linarith
  have hnκ0 : 0 ≤ (n : ℝ) * kappa c := mul_nonneg hn0.le hκ0
  have hXle : X ≤ √2 * r := by
    rw [hX, hr, ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    have e : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * (n * kappa c) := by ring
    rw [e, e8]; linarith
  have hXq : X * q ≤ 141422 / 100000 * (959167 / 100000 * (141422 / 100000)) := by
    calc X * q ≤ √2 * r * q := mul_le_mul_of_nonneg_right hXle hq0
      _ = √2 * (q * r) := by ring
      _ ≤ 141422 / 100000 * (959167 / 100000 * (141422 / 100000)) :=
          mul_le_mul h2 hqrb (by positivity) (by norm_num)
  have hdm2lo : 2 * n * (1 - kappa c) - 76735 / 1000 ≤ s3dm n 46 c ^ 2 := by
    rw [hdm]
    have e : (X - 2 * q) ^ 2 = X ^ 2 - 4 * (X * q) + 4 * q ^ 2 := by ring
    have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
    rw [e, hXX, e8]; linarith
  have h6 : s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 := by
    have h1 : s3dm n 46 c ^ 2 ≤ X ^ 2 := by
      rw [hdm]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [hap]
    have e : (r + q) ^ 2 = r ^ 2 + 2 * (q * r) + q ^ 2 := by ring
    have e2 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * (n * kappa c) := by ring
    have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
    rw [hXX, e2, e8] at h1
    rw [e, hrr]; linarith
  -- `d₊`
  set Y := √(2 * n * (1 - kappa c)) with hY
  have hY0 : 0 ≤ Y := Real.sqrt_nonneg _
  have hYY : Y ^ 2 = 2 * n * (1 - kappa c) := Real.sq_sqrt (by linarith)
  have hYle : Y ≤ √2 * r := by
    rw [hY, hr, ← Real.sqrt_mul (by norm_num)]
    refine Real.sqrt_le_sqrt ?_
    have e : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * (n * kappa c) := by ring
    rw [e]; linarith
  have hYq : Y * q ≤ 141422 / 100000 * (959167 / 100000 * (141422 / 100000)) := by
    calc Y * q ≤ √2 * r * q := mul_le_mul_of_nonneg_right hYle hq0
      _ = √2 * (q * r) := by ring
      _ ≤ 141422 / 100000 * (959167 / 100000 * (141422 / 100000)) :=
          mul_le_mul h2 hqrb (by positivity) (by norm_num)
  have hdp : (Y + 2 * q) ^ 2 ≤ 2 * n * (1 - kappa c) + 76782 / 1000 := by
    have e : (Y + 2 * q) ^ 2 = Y ^ 2 + 4 * (Y * q) + 4 * q ^ 2 := by ring
    rw [e, hYY]; linarith
  exact ⟨hamp, hap2, ham2, hamap, hdm0, hdm2lo, h6, hdp⟩

/-- **`c₁⁺ ≤ C₁`** from `κ(c) ≤ K_U`. -/
theorem t5_c1_le (hn : 16384 ≤ n) {c KU C1 : ℝ} (hκ0 : 0 ≤ kappa c) (hκ : kappa c ≤ KU)
    (hKU : KU ≤ 3 / 4) (hKC : KU ≤ C1)
    (hC : 2 * KU * 16384 + 131020 / 1000 ≤ C1 * (2 * 16384 - 54260 / 1000)) :
    s3c1 n 46 c ≤ C1 := by
  obtain ⟨ham, hap2, ham2, -, -, hdm2, -, -⟩ := t5_geom hn hκ0 (hκ.trans hKU)
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  unfold s3c1
  rw [div_le_iff₀ (by positivity)]
  have hC0 : 0 ≤ C1 := le_trans (hκ0.trans hκ) hKC
  have h1 : 2 * n * kappa c ≤ 2 * n * KU := by
    have : (0 : ℝ) ≤ 2 * n := by positivity
    exact mul_le_mul_of_nonneg_left hκ this
  have h2 : C1 * (2 * n - 54260 / 1000) ≤ C1 * (2 * s3am n 46 ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hC0
  have h3 : 2 * KU * ((n : ℝ) - 16384) ≤ 2 * C1 * ((n : ℝ) - 16384) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  nlinarith

/-- **`c₁⁻ ≥ C₁⁻`** from `κ(c) ≥ K_L`. -/
theorem t5_c1lo_ge (hn : 16384 ≤ n) {c KL C1l : ℝ} (hκ0 : 0 ≤ kappa c) (hκ1 : kappa c ≤ 3 / 4)
    (hκ : KL ≤ kappa c) (hC0 : 0 ≤ C1l) (hKC : C1l ≤ KL)
    (hC : C1l * (2 * 16384 + 54282 / 1000) + 131044 / 1000 ≤ 2 * KL * 16384) :
    C1l ≤ d3_c1lo n 46 c ∧ d3_c1lo n 46 c ≤ 1 := by
  obtain ⟨ham, hap2, ham2, hamap, -, -, -, hdp⟩ := t5_geom hn hκ0 hκ1
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have e : d3_c1lo n 46 c = (2 * s3am n 46 ^ 2 -
      (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2) / (2 * s3ap n 46 ^ 2) := rfl
  have hap0 : 0 < s3ap n 46 ^ 2 := lt_of_lt_of_le (by positivity) hamap
  rw [e]
  constructor
  · rw [le_div_iff₀ (by positivity)]
    have h1 : 2 * n * KL ≤ 2 * n * kappa c := by
      have : (0 : ℝ) ≤ 2 * n := by positivity
      exact mul_le_mul_of_nonneg_left hκ this
    have h2 : C1l * (2 * s3ap n 46 ^ 2) ≤ C1l * (2 * n + 54282 / 1000) :=
      mul_le_mul_of_nonneg_left (by linarith) hC0
    have h3 : 2 * C1l * ((n : ℝ) - 16384) ≤ 2 * KL * ((n : ℝ) - 16384) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  · rw [div_le_one (by positivity)]
    nlinarith [sq_nonneg (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ))))]

/-- `√(a·b) ≤ c` from `a·b ≤ c²` for products of square roots. -/
lemma t5_sqrt_mul_le {a b C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (h : a * b ≤ C ^ 2) :
    √a * √b ≤ C := by
  rw [← Real.sqrt_mul ha]; exact t5_sq_le hC h

/-- `σ ≤ 0.871300 + 20/1378 + 13.5647/16384` when `2k ≤ 0.871300²`. -/
lemma t5_sigma (hn : 16384 ≤ n) {k a0 : ℝ} (hk : 0 ≤ k) (ha0 : 0 ≤ a0) (hk2 : 2 * k ≤ a0 ^ 2) :
    √(2 / ((mA n : ℕ) : ℝ)) * (√(((mA n : ℕ) : ℝ) * k) + √(2 * (n : ℝ)) + √(2 * 46)) ≤
      a0 + 20 / 1280 + 135647 / 10000 / 16384 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := t5_M n
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [hM]; positivity
  have hsq : (16384 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  rw [mul_add, mul_add]
  have a : √(2 / ((mA n : ℕ) : ℝ)) * √(((mA n : ℕ) : ℝ) * k) ≤ a0 := by
    refine t5_sqrt_mul_le (by positivity) ha0 ?_
    have e : 2 / ((mA n : ℕ) : ℝ) * (((mA n : ℕ) : ℝ) * k) = 2 * k := by
      field_simp
    rw [e]; exact hk2
  have b : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * (n : ℝ)) ≤ 20 / 1280 := by
    refine t5_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have d : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * 46) ≤ 135647 / 10000 / 16384 := by
    refine t5_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `e4_b n (M·k) 46 ≤ √n·(a + √2·v + √184·v²)`, `v = 10/1378`, when `2k ≤ a²`. -/
lemma t5_eb (hn : 16384 ≤ n) {k a : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) (hka : 2 * k ≤ a ^ 2) :
    e4_b n (((mA n : ℕ) : ℝ) * k) 46 ≤
      √(n : ℝ) * (a + 141422 / 100000 * (10 / 1280) + 135647 / 10000 * (10 / 1280) ^ 2) := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := t5_M n
  set r := √(n : ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrlo : 128 ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hr0' : 0 < r := by linarith
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := t5_sq_le (by norm_num) (by norm_num)
  have h184 : √(184 : ℝ) ≤ 135647 / 10000 := t5_sq_le (by norm_num) (by norm_num)
  have hrv : 1 ≤ r * (10 / 1280) := by linarith
  unfold e4_b
  rw [mul_add, mul_add, mul_add, mul_add]
  have x1 : √(2 / (n : ℝ)) * √(((mA n : ℕ) : ℝ) * k) ≤ r * a := by
    refine t5_sqrt_mul_le (by positivity) (by positivity) ?_
    rw [hM, mul_pow, hrr]
    have e : 2 / (n : ℝ) * ((n : ℝ) ^ 2 * k) = n * (2 * k) := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left hka hn0.le
  have x2 : √(2 / (n : ℝ)) * √(n : ℝ) ≤ r * (141422 / 100000 * (10 / 1280)) := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * n = 2 := by field_simp
    rw [e]
    have : 141422 / 100000 * 1 ≤ 141422 / 100000 * (r * (10 / 1280)) :=
      mul_le_mul_of_nonneg_left hrv (by norm_num)
    nlinarith
  have x3 : √(2 / (n : ℝ)) * √(2 * 46) ≤ r * (135647 / 10000 * (10 / 1280) ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * (2 * 46) = 184 / r ^ 2 := by rw [hrr]; ring
    rw [e, Real.sqrt_div (by norm_num), Real.sqrt_sq hr0, div_le_iff₀ hr0']
    have h1 : 1 ≤ (r * (10 / 1280)) ^ 2 := by nlinarith
    have : 135647 / 10000 * 1 ≤ 135647 / 10000 * (r * (10 / 1280)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    nlinarith
  linarith

/-- `π₁ = e4_b n 2 46 ≤ 20/1378 + √2 + √184·v`. -/
lemma t5_pi (hn : 16384 ≤ n) :
    e4_b n 2 46 ≤ 20 / 1280 + 141422 / 100000 + 135647 / 10000 * (10 / 1280) := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := t5_sq_le (by norm_num) (by norm_num)
  unfold e4_b
  rw [mul_add, mul_add]
  have x1 : √(2 / (n : ℝ)) * √2 ≤ 20 / 1280 := by
    refine t5_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]; nlinarith
  have x2 : √(2 / (n : ℝ)) * √(n : ℝ) ≤ 141422 / 100000 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * n = 2 := by field_simp
    rw [e]; exact h2
  have x3 : √(2 / (n : ℝ)) * √(2 * 46) ≤ 135647 / 10000 * (10 / 1280) := by
    refine t5_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]; nlinarith
  linarith

/-- The factor of `τ₁`: `√(2/M)(√M + √2 + √92) ≤ √2 + 2/16384 + √184/16384`. -/
lemma t5_tauf (hn : 16384 ≤ n) :
    √(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + √(2 * 46)) ≤
      141422 / 100000 + 2 / 16384 + 135647 / 10000 / 16384 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := t5_M n
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [hM]; positivity
  have hsq : (16384 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := t5_sq_le (by norm_num) (by norm_num)
  rw [mul_add, mul_add]
  have x1 : √(2 / ((mA n : ℕ) : ℝ)) * √((mA n : ℕ) : ℝ) ≤ 141422 / 100000 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / ((mA n : ℕ) : ℝ) * ((mA n : ℕ) : ℝ) = 2 := by field_simp
    rw [e]; exact h2
  have x2 : √(2 / ((mA n : ℕ) : ℝ)) * √2 ≤ 2 / 16384 := by
    refine t5_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have x3 : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * 46) ≤ 135647 / 10000 / 16384 := by
    refine t5_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


/-- `κ(t) ≥ (s + t(3.141592/2 + t + t³/6 + 3t⁵/40))/3.141593` when `s ≤ √(1 − t²)`, `0 ≤ s`. -/
lemma t5_kappa_ge {t s : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 3 / 4) (hs0 : 0 ≤ s) (hs : s ≤ √(1 - t ^ 2)) :
    (s + t * (3141592 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40))) / (3141593 / 1000000) ≤
      kappa t := by
  rw [fsn_kappa_eq]
  have ha := fsn_arcsin_ge h0 h1
  have hp := fsn_pi_lo
  have hp2 := fsn_pi_hi
  have hp0 : 0 < π := Real.pi_pos
  have hnum : s + t * (3141592 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40)) ≤
      √(1 - t ^ 2) + t * (π / 2 + Real.arcsin t) := by
    have : t * (3141592 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40)) ≤
        t * (π / 2 + Real.arcsin t) := mul_le_mul_of_nonneg_left (by linarith) h0
    linarith
  have hn0 : 0 ≤ s + t * (3141592 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40)) := by positivity
  calc (s + t * (3141592 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40))) / (3141593 / 1000000)
      ≤ (s + t * (3141592 / 2000000 + (t + t ^ 3 / 6 + 3 * t ^ 5 / 40))) / π :=
        div_le_div_of_nonneg_left hn0 hp0 hp2.le
    _ ≤ _ := div_le_div_of_nonneg_right hnum hp0.le

/-- `ℓ ≥ √n`. -/
lemma t5_ell_ge (hn : 1 ≤ n) {η : ℝ} (hη : 0 ≤ η) :
    √(n : ℝ) ≤ e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + η)) 46 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold e4_b
  have h1 : √(n : ℝ) ≤ √(2 / (n : ℝ)) * √(((mA n : ℕ) : ℝ) * (1 / 2 + η)) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [t5_M]
    have e : 2 / (n : ℝ) * ((n : ℝ) ^ 2 * (1 / 2 + η)) = n + 2 * η * n := by field_simp
    rw [e]; nlinarith
  have h2 : 0 ≤ √(2 / (n : ℝ)) * (√(n : ℝ) + √(2 * 46)) := by positivity
  nlinarith

/-- **The lower singular-value level**: `e3_bl ≥ r₀(1 − ε) − S₀ε` when `σ ≤ S₀`,
`K_lo ≥ m·k₀` and `r₀² ≤ 2(1 − δ)k₀`. -/
lemma t5_bl_ge {K Klo υ δ ε k0 r0 S0 : ℝ} (hm : 0 < mA n) (hδ1 : δ ≤ 1) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hσ : e3_sig n K υ ≤ S0) (hK : ((mA n : ℕ) : ℝ) * k0 ≤ Klo) (hr0 : 0 ≤ r0)
    (hr : r0 ^ 2 ≤ (1 - δ) * (2 * k0)) :
    r0 * (1 - ε) - S0 * ε ≤ e3_bl n K Klo υ δ ε := by
  unfold e3_bl
  have hM : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  have h1 : r0 ≤ √((1 - δ) * (2 / ((mA n : ℕ) : ℝ)) * Klo) := by
    rw [show r0 = √(r0 ^ 2) from (Real.sqrt_sq hr0).symm]
    apply Real.sqrt_le_sqrt
    have : (1 - δ) * (2 * k0) ≤ (1 - δ) * (2 / ((mA n : ℕ) : ℝ) * Klo) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      rw [div_mul_eq_mul_div, le_div_iff₀ hM]; linarith
    calc r0 ^ 2 ≤ (1 - δ) * (2 * k0) := hr
      _ ≤ (1 - δ) * (2 / ((mA n : ℕ) : ℝ) * Klo) := this
      _ = (1 - δ) * (2 / ((mA n : ℕ) : ℝ)) * Klo := by ring
  have h2 : r0 * (1 - ε) ≤ √((1 - δ) * (2 / ((mA n : ℕ) : ℝ)) * Klo) * (1 - ε) :=
    mul_le_mul_of_nonneg_right h1 (by linarith)
  have h3 : e3_sig n K υ * ε ≤ S0 * ε := mul_le_mul_of_nonneg_right hσ hε0
  linarith

/-- **The net term** at `ε = 1/100`, `δ = 1/8`, `K_lo ≥ 0.336m`, `n ≥ 16 384`: `≤ 2·10⁻¹⁹`. -/
lemma t5_net (hn : 16384 ≤ n) {Klo : ℝ} (hK : ((mA n : ℕ) : ℝ) * (336 / 1000) ≤ Klo) :
    (2 * (gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) * exp (-(Klo * (1 / 8) ^ 2 / 4)) ≤
      2 / 10 ^ 19 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set r := √(n : ℝ) with hr
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hr128 : 128 ≤ r := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  set s := r / 128 with hs
  have hs1 : 1 ≤ s := by rw [hs, le_div_iff₀ (by norm_num)]; linarith
  -- the base
  have hg : (gridN (2 * n) (1 / 100) : ℝ) ≤ √((2 * n : ℕ) : ℝ) / (1 / 100) + 1 := by
    unfold gridN
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h2n : √((2 * n : ℕ) : ℝ) = √2 * r := by
    rw [hr, ← Real.sqrt_mul (by norm_num)]; push_cast; ring_nf
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := t5_sq_le (by norm_num) (by norm_num)
  have hbase : 2 * (gridN (2 * n) (1 / 100) : ℝ) + 1 ≤ 36774 * s := by
    rw [h2n] at hg
    have : √2 * r / (1 / 100) ≤ 141422 / 100000 * r * 100 := by
      rw [div_le_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ r)
      nlinarith
    rw [hs]; nlinarith
  -- `36774 s ≤ exp(9.6 + s)`
  have he1 : (27182818283 / 10 ^ 10 : ℝ) < exp 1 := by
    have := Real.exp_one_gt_d9; norm_num at this ⊢; linarith
  have he10 : (27182818283 / 10 ^ 10 : ℝ) ^ 10 ≤ exp 10 := by
    have e : exp 10 = exp 1 ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) he1.le 10
  have he06 : (1 : ℝ) + 6 / 10 + (6 / 10) ^ 2 / 2 ≤ exp (6 / 10) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have hes : s ≤ exp (s - 1) := by have := Real.add_one_le_exp (s - 1); linarith
  have hexp : 36774 * s ≤ exp (96 / 10 + s) := by
    have e : exp (96 / 10 + s) = exp 10 * exp (6 / 10) * exp (s - 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [e]
    have hc : (36774 : ℝ) ≤ exp 10 * exp (6 / 10) := by
      have : (36774 : ℝ) ≤ (27182818283 / 10 ^ 10 : ℝ) ^ 10 * (1 + 6 / 10 + (6 / 10) ^ 2 / 2) := by
        norm_num
      exact this.trans (mul_le_mul he10 he06 (by norm_num) (Real.exp_pos _).le)
    have := mul_le_mul hc hes (by linarith) (by positivity)
    linarith
  have hpow : (2 * (gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) ≤ exp (2 * n * (96 / 10 + s)) := by
    rw [show (2 * (n : ℝ)) * (96 / 10 + s) = ((2 * n : ℕ) : ℝ) * (96 / 10 + s) by push_cast; ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (hbase.trans hexp) _
  -- the exponent
  have hM := t5_M n
  have hn' : (n : ℝ) = 16384 * s ^ 2 := by rw [← hrr, hs]; ring
  have hexpo : 2 * n * (96 / 10 + s) + -(Klo * (1 / 8) ^ 2 / 4) ≤ -44 := by
    have hK' : (n : ℝ) ^ 2 * (336 / 1000) ≤ Klo := by rw [← hM]; exact hK
    rw [hn'] at hK' ⊢
    have hs2 : 1 ≤ s ^ 2 := by nlinarith
    have hs3 : s ^ 3 ≤ s ^ 4 := by nlinarith
    have hs2' : s ^ 2 ≤ s ^ 4 := by nlinarith
    nlinarith
  calc (2 * (gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) * exp (-(Klo * (1 / 8) ^ 2 / 4))
      ≤ exp (2 * n * (96 / 10 + s)) * exp (-(Klo * (1 / 8) ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = exp (2 * n * (96 / 10 + s) + -(Klo * (1 / 8) ^ 2 / 4)) := by rw [Real.exp_add]
    _ ≤ exp (-44) := Real.exp_le_exp.mpr hexpo
    _ ≤ 2 / 10 ^ 19 := by
        have h44 : (27182818283 / 10 ^ 10 : ℝ) ^ 44 ≤ exp 44 := by
          have e : exp 44 = exp 1 ^ 44 := by rw [← Real.exp_nat_mul]; norm_num
          rw [e]
          exact pow_le_pow_left₀ (by norm_num) he1.le 44
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        refine le_trans ?_ h44
        norm_num

/-- **The final arithmetic of the two-sided bound** (pure real inequality). -/
lemma t5_final2 {N r σ bl ℓ L π₁ τ₁ S0 b0 l0 m0 p0 t0 kE : ℝ} (hrr : r ^ 2 = N) (hrlo : 128 ≤ r)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ S0) (hb0 : 0 ≤ b0) (hbl : b0 ≤ bl) (hbσ : b0 ≤ σ) (hℓ : ℓ ≤ r * l0) (hℓlo : r ≤ ℓ)
    (hL0 : 0 ≤ L) (hL : L ≤ r * m0) (hπ0 : 0 ≤ π₁) (hπ : π₁ ≤ p0) (hτ0 : 0 ≤ τ₁) (hτ : τ₁ ≤ t0)
    (hX : p0 ^ 2 / 16384 ≤ 1 - m0 ^ 2)
    (hfin : (S0 ^ 2 - b0 ^ 2) * l0 ^ 2 / 2 + (S0 ^ 2 + b0 ^ 2) * m0 ^ 2 / 2 +
      (S0 ^ 2 + b0 ^ 2) * p0 ^ 2 / 2 * (10 / 1280) ^ 2 + 2 * t0 * S0 * l0 * (10 / 1280) +
      t0 ^ 2 * (10 / 1280) ^ 2 ≤ kE) :
    (σ ^ 2 + bl ^ 2) / 2 * (L ^ 2 + π₁ ^ 2) + (σ ^ 2 - bl ^ 2) / 2 * ℓ ^ 2 +
      2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 ≤ N * kE := by
  have hr0 : 0 < r := by linarith
  have hS0 : 0 ≤ S0 := hσ0.trans hσ
  have hℓ0 : 0 ≤ ℓ := hr0.le.trans hℓlo
  have hl0 : 0 ≤ r * l0 := hℓ0.trans hℓ
  have hl0' : 0 ≤ l0 := by
    by_contra h; push_neg at h
    have := mul_neg_of_pos_of_neg hr0 h; linarith
  have hp0 : 0 ≤ p0 := hπ0.trans hπ
  have ht0 : 0 ≤ t0 := hτ0.trans hτ
  have hN : 0 ≤ N := by rw [← hrr]; positivity
  have eid : (σ ^ 2 + bl ^ 2) / 2 * (L ^ 2 + π₁ ^ 2) + (σ ^ 2 - bl ^ 2) / 2 * ℓ ^ 2 +
      2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 = σ ^ 2 * (ℓ ^ 2 + L ^ 2 + π₁ ^ 2) / 2 -
        bl ^ 2 * (ℓ ^ 2 - L ^ 2 - π₁ ^ 2) / 2 + 2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 := by ring
  rw [eid]
  have hℓ2 : N ≤ ℓ ^ 2 := by rw [← hrr]; exact pow_le_pow_left₀ hr0.le hℓlo 2
  have hL2 : L ^ 2 ≤ N * m0 ^ 2 := by
    have := pow_le_pow_left₀ hL0 hL 2; rw [mul_pow, hrr] at this; exact this
  have hℓ2' : ℓ ^ 2 ≤ N * l0 ^ 2 := by
    have := pow_le_pow_left₀ hℓ0 hℓ 2; rw [mul_pow, hrr] at this; exact this
  have hπ2 : π₁ ^ 2 ≤ p0 ^ 2 := pow_le_pow_left₀ hπ0 hπ 2
  have h1 : (16384 : ℝ) ≤ N := by
    have := pow_le_pow_left₀ (by norm_num) hrlo 2; rw [hrr] at this; norm_num at this; exact this
  have hX0 : 0 ≤ N - N * m0 ^ 2 - p0 ^ 2 := by
    have h2 : p0 ^ 2 / 16384 * N ≤ (1 - m0 ^ 2) * N := mul_le_mul_of_nonneg_right hX hN
    have h3 : p0 ^ 2 * 16384 ≤ p0 ^ 2 * N := mul_le_mul_of_nonneg_left h1 (sq_nonneg p0)
    have e3 : p0 ^ 2 / 16384 * N = p0 ^ 2 * N / 16384 := by ring
    rw [e3] at h2
    have h4 : p0 ^ 2 ≤ p0 ^ 2 * N / 16384 := by rw [le_div_iff₀ (by norm_num)]; linarith
    linarith
  have hXX : N - N * m0 ^ 2 - p0 ^ 2 ≤ ℓ ^ 2 - L ^ 2 - π₁ ^ 2 := by linarith
  have hbl2 : b0 ^ 2 ≤ bl ^ 2 := pow_le_pow_left₀ hb0 hbl 2
  have hneg : b0 ^ 2 * (N - N * m0 ^ 2 - p0 ^ 2) ≤ bl ^ 2 * (ℓ ^ 2 - L ^ 2 - π₁ ^ 2) :=
    mul_le_mul hbl2 hXX hX0 (sq_nonneg _)
  have hσ2 : σ ^ 2 ≤ S0 ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
  have hσb2 : b0 ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hb0 hbσ 2
  have hA : (σ ^ 2 - b0 ^ 2) * ℓ ^ 2 ≤ (S0 ^ 2 - b0 ^ 2) * (N * l0 ^ 2) :=
    mul_le_mul (by linarith) hℓ2' (sq_nonneg _) (by linarith)
  have hB : (σ ^ 2 + b0 ^ 2) * (L ^ 2 + π₁ ^ 2) ≤ (S0 ^ 2 + b0 ^ 2) * (N * m0 ^ 2 + p0 ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have hpos : σ ^ 2 * (ℓ ^ 2 + L ^ 2 + π₁ ^ 2) - b0 ^ 2 * (ℓ ^ 2 - L ^ 2 - π₁ ^ 2) ≤
      (S0 ^ 2 - b0 ^ 2) * (N * l0 ^ 2) + (S0 ^ 2 + b0 ^ 2) * (N * m0 ^ 2 + p0 ^ 2) := by
    have e : σ ^ 2 * (ℓ ^ 2 + L ^ 2 + π₁ ^ 2) - b0 ^ 2 * (ℓ ^ 2 - L ^ 2 - π₁ ^ 2) =
        (σ ^ 2 - b0 ^ 2) * ℓ ^ 2 + (σ ^ 2 + b0 ^ 2) * (L ^ 2 + π₁ ^ 2) := by ring
    rw [e]; linarith
  have hneg' : b0 ^ 2 * (ℓ ^ 2 - L ^ 2 - π₁ ^ 2) ≤ bl ^ 2 * (ℓ ^ 2 - L ^ 2 - π₁ ^ 2) :=
    mul_le_mul_of_nonneg_right hbl2 (le_trans hX0 hXX)
  have hcross : 2 * τ₁ * (σ * ℓ) ≤ 2 * t0 * (S0 * (r * l0)) := by
    have h5 := mul_le_mul hσ hℓ hℓ0 hS0
    have h6 := mul_le_mul hτ h5 (by positivity) ht0
    linarith
  have hτ2 : τ₁ ^ 2 ≤ t0 ^ 2 := pow_le_pow_left₀ hτ0 hτ 2
  have hv : r ≤ N * (10 / 1280) := by
    have : 128 * r ≤ r * r := mul_le_mul_of_nonneg_right hrlo hr0.le
    rw [← hrr]; nlinarith
  have hv2 : (1 : ℝ) ≤ N * (10 / 1280) ^ 2 := by
    have : N * (10 / 1280) ^ 2 = N / 16384 := by ring
    rw [this, le_div_iff₀ (by norm_num)]; linarith
  have c1 : (S0 ^ 2 + b0 ^ 2) * p0 ^ 2 / 2 * 1 ≤ (S0 ^ 2 + b0 ^ 2) * p0 ^ 2 / 2 * (N * (10 / 1280) ^ 2) :=
    mul_le_mul_of_nonneg_left hv2 (by positivity)
  have c2 : 2 * t0 * S0 * l0 * r ≤ 2 * t0 * S0 * l0 * (N * (10 / 1280)) :=
    mul_le_mul_of_nonneg_left hv (by positivity)
  have c3 : t0 ^ 2 * 1 ≤ t0 ^ 2 * (N * (10 / 1280) ^ 2) := mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)
  have c4 := mul_le_mul_of_nonneg_left hfin hN
  have e5 : 2 * t0 * (S0 * (r * l0)) = 2 * t0 * S0 * l0 * r := by ring
  rw [e5] at hcross
  linarith

/-- `c₁⁻ ≤ c₁⁺` when `c₁⁻ ≥ 0`. -/
theorem t5_c1lo_le (hn : 16384 ≤ n) {c : ℝ} (hκ0 : 0 ≤ kappa c) (hκ1 : kappa c ≤ 3 / 4)
    (h0 : 0 ≤ d3_c1lo n 46 c) : d3_c1lo n 46 c ≤ s3c1 n 46 c := by
  obtain ⟨ham, hap2, ham2, hamap, hdm0, -, -, -⟩ := t5_geom hn hκ0 hκ1
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set Y := √(2 * n * (1 - kappa c)) with hY
  set q := √(2 * (46 : ℝ)) * √(2 / (n : ℝ)) with hq
  have hq0 : 0 ≤ q := by positivity
  have hX : √(2 * n * (1 - kappa c) - 4 * (2 / n)) ≤ Y :=
    Real.sqrt_le_sqrt (by have : 0 ≤ 4 * (2 / (n : ℝ)) := by positivity
                          linarith)
  have hdm : s3dm n 46 c = √(2 * n * (1 - kappa c) - 4 * (2 / n)) - 2 * q := rfl
  have hdmdp : s3dm n 46 c ^ 2 ≤ (Y + 2 * q) ^ 2 :=
    pow_le_pow_left₀ hdm0 (by rw [hdm]; linarith) 2
  have e1 : d3_c1lo n 46 c = (2 * s3am n 46 ^ 2 - (Y + 2 * q) ^ 2) / (2 * s3ap n 46 ^ 2) := rfl
  have hap0 : 0 < s3ap n 46 ^ 2 := lt_of_lt_of_le (by positivity) hamap
  rw [e1] at h0 ⊢
  have hA0 : 0 ≤ 2 * s3am n 46 ^ 2 - (Y + 2 * q) ^ 2 := by
    rwa [le_div_iff₀ (by positivity), zero_mul] at h0
  unfold s3c1
  calc (2 * s3am n 46 ^ 2 - (Y + 2 * q) ^ 2) / (2 * s3ap n 46 ^ 2)
      ≤ (2 * s3am n 46 ^ 2 - (Y + 2 * q) ^ 2) / (2 * s3am n 46 ^ 2) :=
        div_le_div_of_nonneg_left hA0 (by positivity) (by linarith)
    _ ≤ (2 * s3ap n 46 ^ 2 - s3dm n 46 c ^ 2) / (2 * s3am n 46 ^ 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- `P₇(t) = t + t³/6 + 3t⁵/40 + t⁷/10`, `P₅(t) = t + t³/6 + 3t⁵/40`. -/
noncomputable def t5P7 (t : ℝ) : ℝ := t + t ^ 3 / 6 + 3 * t ^ 5 / 40 + t ^ 7 / 10
noncomputable def t5P5 (t : ℝ) : ℝ := t + t ^ 3 / 6 + 3 * t ^ 5 / 40

/-- The `κ` and count part of a cell. -/
theorem t5_cell_k (hn : 16384 ≤ n) {c ca cb Sc Sd KU KL C1 C1l kU kL : ℝ}
    (hca : ca ≤ c) (hcb : c ≤ cb) (hca0 : 0 ≤ ca) (hcb1 : cb ≤ 3 / 4)
    (hSc0 : 0 ≤ Sc) (hSc : 1 - cb ^ 2 ≤ Sc ^ 2) (hSd0 : 0 ≤ Sd) (hSd : Sd ^ 2 ≤ 1 - ca ^ 2)
    (hKU : (Sc + cb * (3141593 / 2000000 + t5P7 cb)) / (3141592 / 1000000) ≤ KU)
    (hKL : KL ≤ (Sd + ca * (3141592 / 2000000 + t5P5 ca)) / (3141593 / 1000000))
    (hKU34 : KU ≤ 3 / 4) (hKC : KU ≤ C1) (hC1 : C1 ≤ 3 / 4)
    (hC : 2 * KU * 16384 + 131020 / 1000 ≤ C1 * (2 * 16384 - 54260 / 1000))
    (hC1l0 : 0 ≤ C1l) (hKCl : C1l ≤ KL) (hC1l : C1l ≤ 3 / 4)
    (hCl : C1l * (2 * 16384 + 54282 / 1000) + 131044 / 1000 ≤ 2 * KL * 16384)
    (hkU : 1 / 2 + t5P7 C1 / (3141592 / 1000000) ≤ kU)
    (hkL : kL ≤ 1 / 2 + t5P5 C1l / (3141593 / 1000000)) :
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 ∧
    kdot (s3c1 n 46 c) ≤ kU ∧ kL ≤ kdot (d3_c1lo n 46 c) ∧
      kdot (d3_c1lo n 46 c) ≤ kdot (s3c1 n 46 c) := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : 0 < mA n := by unfold mA; positivity
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  -- `κ(c)` bounds
  have hc0 : 0 ≤ c := hca0.trans hca
  have hcb0 : 0 ≤ cb := hc0.trans hcb
  have hκcb : kappa c ≤ kappa cb :=
    kappa_monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hcb
  have hκca : kappa ca ≤ kappa c :=
    kappa_monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hca
  have hκU : kappa c ≤ KU := by
    have := fsn_kappa_le hcb0 hcb1 (t5_sq_le hSc0 hSc)
    unfold t5P7 at hKU
    linarith
  have hκL : KL ≤ kappa c := by
    have := t5_kappa_ge hca0 (hca.trans (hcb.trans hcb1)) hSd0
      (Real.le_sqrt_of_sq_le hSd)
    unfold t5P5 at hKL
    linarith
  have hκ0 : 0 ≤ kappa c := le_trans (hC1l0.trans hKCl) hκL
  have hκ34 : kappa c ≤ 3 / 4 := hκU.trans hKU34
  obtain ⟨hamp, hap2, ham2, hamap, hdm0, hdm2, h6, hdp⟩ := t5_geom hn hκ0 hκ34
  -- (i)
  have hi : (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 := by
    have e : s3am n 46 = √((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ)) := rfl
    rw [← e]
    have h1 : 2 * n * KL ≤ 2 * n * kappa c :=
      mul_le_mul_of_nonneg_left hκL (by positivity)
    have h2 : 2 * 16384 * KL ≤ 2 * n * KL :=
      mul_le_mul_of_nonneg_right (by linarith) (hC1l0.trans hKCl)
    have h3 : 0 ≤ C1l * (2 * 16384 + 54282 / 1000) := by positivity
    linarith
  -- `c₁⁺`, `c₁⁻` and the counts
  have hc1 := t5_c1_le hn hκ0 hκU hKU34 hKC hC
  obtain ⟨hc1l, hc1l1⟩ := t5_c1lo_ge hn hκ0 hκ34 hκL hC1l0 hKCl hCl
  have hc1n : 0 ≤ s3c1 n 46 c := by
    unfold s3c1; apply div_nonneg (by linarith) (by positivity)
  have hkd : kdot (s3c1 n 46 c) ≤ kU := by
    have h1 := kdot_monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hc1
    have h2 := fsn_kdot_le (le_trans hc1n hc1) hC1
    unfold t5P7 at hkU
    linarith
  have hkdl : kL ≤ kdot (d3_c1lo n 46 c) := by
    have h1 := kdot_monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, hc1l1⟩ hc1l
    have h2 := fsn_kdot_ge hC1l0 hC1l
    unfold t5P5 at hkL
    linarith
  have hcc : d3_c1lo n 46 c ≤ s3c1 n 46 c := t5_c1lo_le hn hκ0 hκ34 (hC1l0.trans hc1l)
  have hkk := kdot_monotoneOn ⟨by linarith, hc1l1⟩ ⟨by linarith, by linarith⟩ hcc
  exact ⟨hi, hkd, hkdl, hkk⟩

/-- **The two-sided E-block conditions of `d4_num` on one cell `[c_a, c_b]`** (`τ = 46`,
`η = 293/10⁶`, `δ = 1/8`, `ε = 1/100`, window top `c₊ = cp`, `n ≥ 16 384`). All hypotheses are numeric. -/
theorem t5_cell (hn : 16384 ≤ n) {c ca cb Sc Sd KU KL C1 C1l kU kL cp k655 a2 al am r0 S0 b0 l0 m0 p0 t0
    kE : ℝ} (hca : ca ≤ c) (hcb : c ≤ cb) (hca0 : 0 ≤ ca) (hcb1 : cb ≤ 3 / 4)
    (hSc0 : 0 ≤ Sc) (hSc : 1 - cb ^ 2 ≤ Sc ^ 2) (hSd0 : 0 ≤ Sd) (hSd : Sd ^ 2 ≤ 1 - ca ^ 2)
    (hKU : (Sc + cb * (3141593 / 2000000 + t5P7 cb)) / (3141592 / 1000000) ≤ KU)
    (hKL : KL ≤ (Sd + ca * (3141592 / 2000000 + t5P5 ca)) / (3141593 / 1000000))
    (hKU34 : KU ≤ 3 / 4) (hKC : KU ≤ C1) (hC1 : C1 ≤ 3 / 4)
    (hC : 2 * KU * 16384 + 131020 / 1000 ≤ C1 * (2 * 16384 - 54260 / 1000))
    (hC1l0 : 0 ≤ C1l) (hKCl : C1l ≤ KL) (hC1l : C1l ≤ 3 / 4)
    (hCl : C1l * (2 * 16384 + 54282 / 1000) + 131044 / 1000 ≤ 2 * KL * 16384)
    (hkU : 1 / 2 + t5P7 C1 / (3141592 / 1000000) ≤ kU)
    (hkL : kL ≤ 1 / 2 + t5P5 C1l / (3141593 / 1000000))
    (hcp0 : 0 ≤ cp) (hcp1 : cp ≤ 3 / 4) (hk655 : 1 / 2 + t5P7 cp / (3141592 / 1000000) ≤ k655)
    (ha2 : 0 ≤ a2) (ha2' : 2 * (kU / 2 + 293 / 1000000) ≤ a2 ^ 2)
    (hal : 0 ≤ al) (hal' : 2 * (1 / 2 + 293 / 1000000) ≤ al ^ 2)
    (ham : 0 ≤ am) (ham' : 2 * (k655 / 2 + 293 / 1000000) ≤ am ^ 2)
    (hklo : 336 / 1000 ≤ kL / 2 - 293 / 1000000)
    (hr0 : 0 ≤ r0) (hr0' : r0 ^ 2 ≤ (1 - 1 / 8) * (2 * (kL / 2 - 293 / 1000000)))
    (hS0 : a2 + 20 / 1280 + 135647 / 10000 / 16384 ≤ S0)
    (hb0 : b0 ≤ r0 * (1 - 1 / 100) - S0 * (1 / 100)) (hb00 : 0 ≤ b0)
    (hl0 : al + 141422 / 100000 * (10 / 1280) + 135647 / 10000 * (10 / 1280) ^ 2 ≤ l0)
    (hm0 : am + 141422 / 100000 * (10 / 1280) + 135647 / 10000 * (10 / 1280) ^ 2 ≤ m0)
    (hp0 : 20 / 1280 + 141422 / 100000 + 135647 / 10000 * (10 / 1280) ≤ p0)
    (ht0 : (141422 / 100000 + 2 / 16384 + 135647 / 10000 / 16384) * p0 ≤ t0)
    (hX : p0 ^ 2 / 16384 ≤ 1 - m0 ^ 2)
    (hfin : (S0 ^ 2 - b0 ^ 2) * l0 ^ 2 / 2 + (S0 ^ 2 + b0 ^ 2) * m0 ^ 2 / 2 +
      (S0 ^ 2 + b0 ^ 2) * p0 ^ 2 / 2 * (10 / 1280) ^ 2 + 2 * t0 * S0 * l0 * (10 / 1280) +
      t0 ^ 2 * (10 / 1280) ^ 2 ≤ kE) :
    (√(2 * n * (1 - kappa c)) + 2 * (√(2 * 46) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√((n : ℝ) - 2 / n) - √(2 * 46) * √(2 / (n : ℝ))) ^ 2 ∧
    0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000) ∧
    0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000)) (√(2 * 46)) (1 / 8) (1 / 100) ∧
    (2 * (gridN (2 * n) (1 / 100) : ℝ) + 1) ^ (2 * n) *
      exp (-(((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000) * (1 / 8) ^ 2 / 4)) ≤
        2 / 10 ^ 19 ∧
    e3_bound2 n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000)) (√(2 * 46))
      (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + 293 / 1000000)) 46)
      (e4_b n (((mA n : ℕ) : ℝ) * (kdot cp / 2 + 293 / 1000000)) 46 ^ 2)
      (e4_b n 2 46) (1 / 8) (1 / 100) ≤ n * kE := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hm : 0 < mA n := by unfold mA; positivity
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
  obtain ⟨hi, hkd, hkdl, hkk⟩ := t5_cell_k hn hca hcb hca0 hcb1 hSc0 hSc hSd0 hSd hKU hKL hKU34 hKC hC1
    hC hC1l0 hKCl hC1l hCl hkU hkL
  have hKlo : ((mA n : ℕ) : ℝ) * (kL / 2 - 293 / 1000000) ≤
      ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000) :=
    mul_le_mul_of_nonneg_left (by linarith) hM0.le
  have hii : 0 ≤ ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000) := by
    have : 0 ≤ ((mA n : ℕ) : ℝ) * (kL / 2 - 293 / 1000000) := mul_nonneg hM0.le (by linarith)
    linarith
  -- `σ`
  have hkn := kdot_nonneg (s3c1 n 46 c)
  have hσ : e3_sig n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000)) (√(2 * 46)) ≤
      S0 := by
    have h := t5_sigma hn (k := kdot (s3c1 n 46 c) / 2 + 293 / 1000000) (a0 := a2) (by positivity) ha2
      (by linarith)
    exact h.trans hS0
  have hσ0 : 0 ≤ e3_sig n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
      (√(2 * 46)) := by unfold e3_sig; positivity
  -- `bl`
  have hbl := t5_bl_ge (n := n) (K := ((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
    (υ := √(2 * 46)) hm (by norm_num : (1 / 8 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    (by norm_num : (1 / 100 : ℝ) ≤ 1) hσ hKlo hr0 hr0'
  have hiii : 0 ≤ e3_bl n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
      (((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000)) (√(2 * 46)) (1 / 8)
        (1 / 100) := by linarith
  -- net
  have hiv := t5_net hn (Klo := ((mA n : ℕ) : ℝ) * (kdot (d3_c1lo n 46 c) / 2 - 293 / 1000000))
    (by have : ((mA n : ℕ) : ℝ) * (336 / 1000) ≤ ((mA n : ℕ) : ℝ) * (kL / 2 - 293 / 1000000) :=
          mul_le_mul_of_nonneg_left hklo hM0.le
        linarith)
  refine ⟨hi, hii, hiii, hiv, ?_⟩
  -- the bound
  have hrr : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hrlo : 128 ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hl := t5_eb hn (k := 1 / 2 + 293 / 1000000) (a := al) (by norm_num) hal hal'
  have hk655n := kdot_nonneg cp
  have hk655' : kdot cp ≤ k655 := by
    have := fsn_kdot_le (t := cp) hcp0 hcp1
    unfold t5P7 at hk655
    linarith
  have hmm := t5_eb hn (k := kdot cp / 2 + 293 / 1000000) (a := am) (by positivity) ham
    (by linarith)
  have hp := t5_pi hn
  have htf := t5_tauf hn
  have hp00 : 0 ≤ e4_b n 2 46 := by unfold e4_b; positivity
  have hτ := mul_le_mul htf (hp.trans hp0) hp00 (by norm_num)
  have hlo := t5_ell_ge (n := n) (by omega) (η := 293 / 1000000) (by norm_num)
  have hbσ := d2_bl_le_sig (n := n) (K := ((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 293 / 1000000))
    (υ := √(2 * 46)) hii (mul_le_mul_of_nonneg_left (by linarith) hM0.le)
    (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num : (1 / 8 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) < 1 / 100)
    (by norm_num : (1 / 100 : ℝ) < 1) (Real.sqrt_nonneg _)
  unfold e3_bound2
  exact t5_final2 hrr hrlo hσ0 hσ hb00 (hb0.trans hbl) ((hb0.trans hbl).trans hbσ) (hl.trans (by gcongr)) hlo
    (by unfold e4_b; positivity) (hmm.trans (by gcongr)) hp00 (hp.trans hp0) (by positivity)
    (hτ.trans ht0) hX hfin

end BstLean.Part186.T
