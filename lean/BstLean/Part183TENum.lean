import BstLean.Part182EBlk4
import BstLean.Part159Kap

/-!
# Part 183 (file `TENum`): the E-block numerics of Lemma TI (TI-lite) at `n ≥ 20 000`

No proof is left open; no `native_decide` or `axiom` is used. Rational constants were chosen with a
single-process python calculator; Lean checks every inequality.

A copy of Part 182's file `ENum` (names prefixed `t`, namespace `BstLean.Part183.T`) with the floor
`20 000`, `c₊ = 0.646`, `η = 24/100000`:
* `ten_kappa_le`: `κ(c) ≤ 0.71128` for `c ≤ 0.646`.
* `ten_side`: the side conditions of `e4_Eblock` and `s3c1 ≤ 0.71553`.
* `ten_eta`: `46 ≤ 2η²·mA n` (`η = 0.00024`, `n ≥ 20 000`).
* **`ten_kE`**: the bound of `e4_Eblock` is at most `0.72·n` (exact value at `n = 20 000`,
  `c = 0.646`: `≈ 0.7151·n`; certified `≈ 0.7190·n`).
-/

namespace BstLean.Part183.T

open BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130

variable {n : ℕ}

lemma ten_M (n : ℕ) : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring

/-! ## Trigonometric enclosures -/

lemma ten_sin_lb {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : t - t ^ 3 / 6 - t ^ 5 / 100 ≤ Real.sin t := by
  have h := Real.sin_bound (x := t) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at h
  have := (abs_le.1 h).1
  linarith

lemma ten_arcsin_le {x θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hx : x ≤ θ - θ ^ 3 / 6 - θ ^ 5 / 100) :
    Real.arcsin x ≤ θ := by
  have hs := ten_sin_lb h0 h1
  have hpi := Real.pi_gt_three
  have h2 : Real.arcsin x ≤ Real.arcsin (Real.sin θ) := Real.monotone_arcsin (hx.trans hs)
  rwa [Real.arcsin_sin (by linarith) (by linarith)] at h2

lemma ten_kdot_eq (q : ℝ) : kdot q = 1 / 2 + Real.arcsin q / π := by
  unfold kdot
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have hp := Real.pi_pos
  field_simp
  ring

lemma ten_kdot_le {q θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (hq : q ≤ θ - θ ^ 3 / 6 - θ ^ 5 / 100) :
    kdot q ≤ 1 / 2 + θ / (314159 / 100000) := by
  rw [ten_kdot_eq]
  have ha := ten_arcsin_le h0 h1 hq
  have hp := Real.pi_gt_d6
  have hpp : (314159 / 100000 : ℝ) ≤ π := by norm_num at hp ⊢; linarith
  have hθ : Real.arcsin q / π ≤ θ / π := div_le_div_of_nonneg_right ha Real.pi_pos.le
  have hθ2 : θ / π ≤ θ / (314159 / 100000) := div_le_div_of_nonneg_left h0 (by norm_num) hpp
  linarith

/-- `κ(c) ≤ 0.70761` for `−1 ≤ c ≤ 0.641`. -/
lemma ten_kappa_le {c : ℝ} (h0 : -1 ≤ c) (h1 : c ≤ 646 / 1000) : kappa c ≤ 71128 / 100000 := by
  have hm := kappa_monotoneOn ⟨h0, h1.trans (by norm_num)⟩ ⟨by norm_num, by norm_num⟩ h1
  refine hm.trans ?_
  rw [BstLean.Part159.kappa_arcsin]
  have ha := ten_arcsin_le (x := 646 / 1000) (θ := 3533 / 5000) (by norm_num) (by norm_num)
    (by norm_num)
  have hs : √(1 - (646 / 1000 : ℝ) ^ 2) ≤ 381669 / 500000 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hp := Real.pi_gt_d6
  have hpp : (314159 / 100000 : ℝ) ≤ π := by norm_num at hp ⊢; linarith
  have hπ0 := Real.pi_pos
  rw [div_le_iff₀ hπ0]
  have hnum : √(1 - (646 / 1000 : ℝ) ^ 2) + 646 / 1000 * (π / 2 + Real.arcsin (646 / 1000)) ≤
      381669 / 500000 + 646 / 1000 * (π / 2 + 3533 / 5000) := by
    have : 646 / 1000 * Real.arcsin (646 / 1000) ≤ 646 / 1000 * (3533 / 5000 : ℝ) :=
      mul_le_mul_of_nonneg_left ha (by norm_num)
    nlinarith
  nlinarith

/-! ## The side conditions and `c₁⁺ ≤ 0.71203` -/

lemma ten_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ≤ b ^ 2) : √a ≤ b :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hb))

/-- **The side conditions of `e4_Eblock` and `c₁⁺ ≤ 0.71203`** at `τ = 46`, `n ≥ 21 000`,
`−1 ≤ c ≤ 0.641`. -/
theorem ten_side (hn : 20000 ≤ n) {c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 646 / 1000) :
    0 < s3am n 46 ∧ 0 ≤ s3dm n 46 c ∧ s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 ∧
      s3c1 n 46 c ≤ 71553 / 100000 := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hκ := ten_kappa_le hc0 hc1
  have hκ0 := (kappa_mem hc0 (hc1.trans (by norm_num))).1
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
  have h92 : √(2 * (46 : ℝ)) ≤ 959167 / 100000 := ten_sq_le (by norm_num) (by norm_num)
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := ten_sq_le (by norm_num) (by norm_num)
  have hqrb : q * r ≤ 959167 / 100000 * (141422 / 100000) := by
    rw [hqr]; exact mul_le_mul h92 h2 (Real.sqrt_nonneg _) (by norm_num)
  have hinv : 1 / (n : ℝ) ≤ 1 / 20000 := one_div_le_one_div_of_le (by norm_num) hnR
  have hq2 : q ^ 2 ≤ 184 / 20000 := by
    rw [hqq]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  -- `a₊`
  have hap : s3ap n 46 = r + q := rfl
  -- `a₋`
  set s := √((n : ℝ) - 2 / n) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hn2 : 0 ≤ (n : ℝ) - 2 / n := by
    have : 2 / (n : ℝ) ≤ 2 / 20000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
    linarith
  have hss : s ^ 2 = (n : ℝ) - 2 / n := Real.sq_sqrt hn2
  have hsr : s ≤ r := Real.sqrt_le_sqrt (by
    have : 0 ≤ 2 / (n : ℝ) := by positivity
    linarith)
  have ham : s3am n 46 = s - q := rfl
  have hsq : q < s := by
    have h1 : q ^ 2 < s ^ 2 := by
      rw [hqq, hss]
      have : 186 / (n : ℝ) ≤ 186 / 20000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
      have e : 184 / (n : ℝ) + 2 / n = 186 / n := by ring
      linarith
    exact (pow_lt_pow_iff_left₀ hq0 hs0 two_ne_zero).1 h1
  have hamp : 0 < s3am n 46 := by rw [ham]; linarith
  have ham2 : (n : ℝ) - 2 / n - 2 * (q * r) ≤ s3am n 46 ^ 2 := by
    rw [ham]
    have h1 : s * q ≤ r * q := mul_le_mul_of_nonneg_right hsr hq0
    have e : (s - q) ^ 2 = s ^ 2 - 2 * (s * q) + q ^ 2 := by ring
    have e2 : r * q = q * r := by ring
    have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
    rw [e, hss]; linarith
  -- `d₋`
  set X := √(2 * n * (1 - kappa c) - 4 * (2 / n)) with hX
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have h1κ : (28872 : ℝ) / 100000 ≤ 1 - kappa c := by linarith
  have h2nκ : 2 * 20000 * (28872 / 100000 : ℝ) ≤ 2 * n * (1 - kappa c) := by
    have := mul_le_mul hnR h1κ (by norm_num) hn0.le
    linarith
  have e8 : 4 * (2 / (n : ℝ)) = 8 / n := by ring
  have h8n : 8 / (n : ℝ) ≤ 8 / 20000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  have h8n0 : 0 ≤ 8 / (n : ℝ) := by positivity
  have harg : 0 ≤ 2 * n * (1 - kappa c) - 4 * (2 / (n : ℝ)) := by
    rw [e8]; linarith
  have hXX : X ^ 2 = 2 * n * (1 - kappa c) - 4 * (2 / n) := Real.sq_sqrt harg
  have hdm : s3dm n 46 c = X - 2 * q := rfl
  have hX2q : 2 * q ≤ X := by
    have h1 : (2 * q) ^ 2 ≤ X ^ 2 := by
      have e : (2 * q) ^ 2 = 736 / n := by rw [mul_pow, hqq]; ring
      have : 736 / (n : ℝ) ≤ 736 / 20000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
      rw [e, hXX, e8]; linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hX0 two_ne_zero).1 h1
  have hdm0 : 0 ≤ s3dm n 46 c := by rw [hdm]; linarith
  have hnκ : (n : ℝ) * kappa c ≤ n * (71128 / 100000) := mul_le_mul_of_nonneg_left hκ hn0.le
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
  have hdm2lo : 2 * n * (1 - 71128 / 100000) - 8 / n -
      4 * (141422 / 100000 * (959167 / 100000 * (141422 / 100000))) ≤ s3dm n 46 c ^ 2 := by
    rw [hdm]
    have e : (X - 2 * q) ^ 2 = X ^ 2 - 4 * (X * q) + 4 * q ^ 2 := by ring
    have e2 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * (n * kappa c) := by ring
    have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
    rw [e, hXX, e8, e2]; linarith
  have h6 : s3dm n 46 c ^ 2 ≤ 2 * s3ap n 46 ^ 2 := by
    have h1 : s3dm n 46 c ^ 2 ≤ X ^ 2 := by
      rw [hdm]; exact pow_le_pow_left₀ (by linarith) (by linarith) 2
    rw [hap]
    have e : (r + q) ^ 2 = r ^ 2 + 2 * (q * r) + q ^ 2 := by ring
    have e2 : 2 * (n : ℝ) * (1 - kappa c) = 2 * n - 2 * (n * kappa c) := by ring
    have hqr0 : 0 ≤ q * r := mul_nonneg hq0 hr0
    have hq2' : 0 ≤ q ^ 2 := sq_nonneg q
    rw [hXX, e2, e8] at h1
    rw [e, hrr]; linarith
  refine ⟨hamp, hdm0, h6, ?_⟩
  -- `c₁⁺`
  unfold s3c1
  rw [div_le_iff₀ (by positivity)]
  rw [hap]
  have e : (r + q) ^ 2 = r ^ 2 + 2 * (q * r) + q ^ 2 := by ring
  have h2n : 2 / (n : ℝ) ≤ 2 / 20000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  rw [e, hrr]
  linarith

/-- `46 ≤ 2η²·mA n` for `η = 23/100000` and `n ≥ 21 000`. -/
lemma ten_eta (hn : 20000 ≤ n) : (46 : ℝ) ≤ 2 * (24 / 100000) ^ 2 * ((mA n : ℕ) : ℝ) := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  rw [ten_M]
  have : (20000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  nlinarith

/-! ## The E-block constant `k_E ≤ 0.715` -/

/-- `√(a·b) ≤ c` from `a·b ≤ c²` for products of square roots. -/
lemma ten_sqrt_mul_le {a b C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (h : a * b ≤ C ^ 2) :
    √a * √b ≤ C := by
  rw [← Real.sqrt_mul ha]; exact ten_sq_le hC h

/-- `σ ≤ 0.870153 + 20/1414 + 13.5647/20000` when `2k ≤ 0.870153²`. -/
lemma ten_sigma (hn : 20000 ≤ n) {k : ℝ} (hk : 0 ≤ k) (hk2 : 2 * k ≤ (870153 / 1000000) ^ 2) :
    √(2 / ((mA n : ℕ) : ℝ)) * (√(((mA n : ℕ) : ℝ) * k) + √(2 * (n : ℝ)) + √(2 * 46)) ≤
      870153 / 1000000 + 20 / 1414 + 135647 / 10000 / 20000 := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := ten_M n
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [hM]; positivity
  have hsq : (20000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  rw [mul_add, mul_add]
  have a : √(2 / ((mA n : ℕ) : ℝ)) * √(((mA n : ℕ) : ℝ) * k) ≤ 870153 / 1000000 := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    have e : 2 / ((mA n : ℕ) : ℝ) * (((mA n : ℕ) : ℝ) * k) = 2 * k := by
      field_simp
    rw [e]; exact hk2
  have b : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * (n : ℝ)) ≤ 20 / 1414 := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have d : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * 46) ≤ 135647 / 10000 / 20000 := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `e4_b n (M·k) 46 ≤ √n·(a + √2·v + √184·v²)`, `v = 10/1414`, when `2k ≤ a²`. -/
lemma ten_eb (hn : 20000 ≤ n) {k a : ℝ} (hk : 0 ≤ k) (ha : 0 ≤ a) (hka : 2 * k ≤ a ^ 2) :
    e4_b n (((mA n : ℕ) : ℝ) * k) 46 ≤
      √(n : ℝ) * (a + 141422 / 100000 * (10 / 1414) + 135647 / 10000 * (10 / 1414) ^ 2) := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := ten_M n
  set r := √(n : ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = n := Real.sq_sqrt hn0.le
  have hrlo : 1414 / 10 ≤ r := by
    rw [hr]; exact Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hr0' : 0 < r := by linarith
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := ten_sq_le (by norm_num) (by norm_num)
  have h184 : √(184 : ℝ) ≤ 135647 / 10000 := ten_sq_le (by norm_num) (by norm_num)
  have hrv : 1 ≤ r * (10 / 1414) := by linarith
  unfold e4_b
  rw [mul_add, mul_add, mul_add, mul_add]
  have x1 : √(2 / (n : ℝ)) * √(((mA n : ℕ) : ℝ) * k) ≤ r * a := by
    refine ten_sqrt_mul_le (by positivity) (by positivity) ?_
    rw [hM, mul_pow, hrr]
    have e : 2 / (n : ℝ) * ((n : ℝ) ^ 2 * k) = n * (2 * k) := by field_simp
    rw [e]; exact mul_le_mul_of_nonneg_left hka hn0.le
  have x2 : √(2 / (n : ℝ)) * √(n : ℝ) ≤ r * (141422 / 100000 * (10 / 1414)) := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * n = 2 := by field_simp
    rw [e]
    have : 141422 / 100000 * 1 ≤ 141422 / 100000 * (r * (10 / 1414)) :=
      mul_le_mul_of_nonneg_left hrv (by norm_num)
    nlinarith
  have x3 : √(2 / (n : ℝ)) * √(2 * 46) ≤ r * (135647 / 10000 * (10 / 1414) ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * (2 * 46) = 184 / r ^ 2 := by rw [hrr]; ring
    rw [e, Real.sqrt_div (by norm_num), Real.sqrt_sq hr0, div_le_iff₀ hr0']
    have h1 : 1 ≤ (r * (10 / 1414)) ^ 2 := by nlinarith
    have : 135647 / 10000 * 1 ≤ 135647 / 10000 * (r * (10 / 1414)) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    nlinarith
  linarith

/-- `π₁ = e4_b n 2 46 ≤ 20/1414 + √2 + √184·v`. -/
lemma ten_pi (hn : 20000 ≤ n) :
    e4_b n 2 46 ≤ 20 / 1414 + 141422 / 100000 + 135647 / 10000 * (10 / 1414) := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := ten_sq_le (by norm_num) (by norm_num)
  unfold e4_b
  rw [mul_add, mul_add]
  have x1 : √(2 / (n : ℝ)) * √2 ≤ 20 / 1414 := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]; nlinarith
  have x2 : √(2 / (n : ℝ)) * √(n : ℝ) ≤ 141422 / 100000 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / (n : ℝ) * n = 2 := by field_simp
    rw [e]; exact h2
  have x3 : √(2 / (n : ℝ)) * √(2 * 46) ≤ 135647 / 10000 * (10 / 1414) := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hn0]; nlinarith
  linarith

/-- The factor of `τ₁`: `√(2/M)(√M + √2 + √92) ≤ √2 + 2/20000 + √184/20000`. -/
lemma ten_tauf (hn : 20000 ≤ n) :
    √(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √2 + √(2 * 46)) ≤
      141422 / 100000 + 2 / 20000 + 135647 / 10000 / 20000 := by
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM := ten_M n
  have hM0 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by rw [hM]; positivity
  have hsq : (20000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
  have h2 : √(2 : ℝ) ≤ 141422 / 100000 := ten_sq_le (by norm_num) (by norm_num)
  rw [mul_add, mul_add]
  have x1 : √(2 / ((mA n : ℕ) : ℝ)) * √((mA n : ℕ) : ℝ) ≤ 141422 / 100000 := by
    rw [← Real.sqrt_mul (by positivity)]
    have e : 2 / ((mA n : ℕ) : ℝ) * ((mA n : ℕ) : ℝ) = 2 := by field_simp
    rw [e]; exact h2
  have x2 : √(2 / ((mA n : ℕ) : ℝ)) * √2 ≤ 2 / 20000 := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have x3 : √(2 / ((mA n : ℕ) : ℝ)) * √(2 * 46) ≤ 135647 / 10000 / 20000 := by
    refine ten_sqrt_mul_le (by positivity) (by norm_num) ?_
    rw [hM, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

/-- The final arithmetic (pure real inequality). -/
lemma ten_final {N r σ ℓ L π₁ τ₁ S0 l0 m0 p0 t0 : ℝ} (hrr : r ^ 2 = N) (hrlo : 1414 / 10 ≤ r)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ S0) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ r * l0) (hL0 : 0 ≤ L) (hL : L ≤ r * m0)
    (hπ0 : 0 ≤ π₁) (hπ : π₁ ≤ p0) (hτ0 : 0 ≤ τ₁) (hτ : τ₁ ≤ t0)
    (hfin : S0 ^ 2 * (l0 ^ 2 + m0 ^ 2) / 2 + S0 ^ 2 * p0 ^ 2 / 2 * (10 / 1414) ^ 2 +
      2 * t0 * S0 * l0 * (10 / 1414) + t0 ^ 2 * (10 / 1414) ^ 2 ≤ 72 / 100) :
    σ ^ 2 * (ℓ ^ 2 + (L ^ 2 + π₁ ^ 2)) / 2 + 2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 ≤ N * (72 / 100) := by
  have hr0 : 0 < r := by linarith
  have hS0 : 0 ≤ S0 := hσ0.trans hσ
  have hl0 : 0 ≤ r * l0 := hℓ0.trans hℓ
  have hm0 : 0 ≤ r * m0 := hL0.trans hL
  have hp0 : 0 ≤ p0 := hπ0.trans hπ
  have ht0 : 0 ≤ t0 := hτ0.trans hτ
  have h1 : σ ^ 2 * (ℓ ^ 2 + (L ^ 2 + π₁ ^ 2)) / 2 + 2 * τ₁ * (σ * ℓ) + τ₁ ^ 2 ≤
      S0 ^ 2 * ((r * l0) ^ 2 + ((r * m0) ^ 2 + p0 ^ 2)) / 2 + 2 * t0 * (S0 * (r * l0)) + t0 ^ 2 := by
    gcongr
  refine h1.trans ?_
  have hl0' : 0 ≤ l0 := by
    by_contra h; push_neg at h; nlinarith
  have hv : r ≤ N * (10 / 1414) := by rw [← hrr]; nlinarith
  have hv2 : (1 : ℝ) ≤ N * (10 / 1414) ^ 2 := by rw [← hrr]; nlinarith
  have e : S0 ^ 2 * ((r * l0) ^ 2 + ((r * m0) ^ 2 + p0 ^ 2)) / 2 + 2 * t0 * (S0 * (r * l0)) + t0 ^ 2
      = N * (S0 ^ 2 * (l0 ^ 2 + m0 ^ 2) / 2) + S0 ^ 2 * p0 ^ 2 / 2 * 1 +
        2 * t0 * S0 * l0 * r + t0 ^ 2 * 1 := by
    rw [← hrr]; ring
  rw [e]
  have c1 : S0 ^ 2 * p0 ^ 2 / 2 * 1 ≤ S0 ^ 2 * p0 ^ 2 / 2 * (N * (10 / 1414) ^ 2) :=
    mul_le_mul_of_nonneg_left hv2 (by positivity)
  have c2 : 2 * t0 * S0 * l0 * r ≤ 2 * t0 * S0 * l0 * (N * (10 / 1414)) :=
    mul_le_mul_of_nonneg_left hv (by positivity)
  have c3 : t0 ^ 2 * 1 ≤ t0 ^ 2 * (N * (10 / 1414) ^ 2) :=
    mul_le_mul_of_nonneg_left hv2 (by positivity)
  have hN : 0 ≤ N := by rw [← hrr]; positivity
  have c4 := mul_le_mul_of_nonneg_left hfin hN
  nlinarith

/-- **The E-block numerics**: for `n ≥ 21 000`, `−1 ≤ c ≤ 0.641`, `τ = 46`, `η = 0.00023`,
`c₊ = 0.641`, the bound of `e4_Eblock` is at most `0.715·n`. -/
theorem ten_kE (hn : 20000 ≤ n) {c : ℝ} (hc0 : -1 ≤ c) (hc1 : c ≤ 646 / 1000) :
    e3_bound n (((mA n : ℕ) : ℝ) * (kdot (s3c1 n 46 c) / 2 + 24 / 100000)) (√(2 * 46))
      (e4_b n (((mA n : ℕ) : ℝ) * (1 / 2 + 24 / 100000)) 46)
      (e4_b n (((mA n : ℕ) : ℝ) * (kdot (646 / 1000) / 2 + 24 / 100000)) 46 ^ 2)
      (e4_b n 2 46) ≤ n * (72 / 100) := by
  obtain ⟨ham, hdm, h6, hc1p⟩ := ten_side hn hc0 hc1
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc1nn : 0 ≤ s3c1 n 46 c := by
    unfold s3c1; apply div_nonneg (by linarith) (by positivity)
  have hk2 : kdot (s3c1 n 46 c) ≤ 1 / 2 + 504 / 625 / (314159 / 100000) :=
    (kdot_monotoneOn ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ hc1p).trans
      (ten_kdot_le (by norm_num) (by norm_num) (by norm_num))
  have hk11 : kdot (646 / 1000) ≤ 1 / 2 + 3533 / 5000 / (314159 / 100000) :=
    ten_kdot_le (by norm_num) (by norm_num) (by norm_num)
  have hk2n := kdot_nonneg (s3c1 n 46 c)
  have hk11n := kdot_nonneg (646 / 1000)
  have hσ := ten_sigma hn (k := kdot (s3c1 n 46 c) / 2 + 24 / 100000) (by positivity)
    (by have : 2 * ((1 / 2 + 504 / 625 / (314159 / 100000)) / 2 + 24 / 100000 : ℝ) ≤
            (870153 / 1000000) ^ 2 := by norm_num
        linarith)
  have hl := ten_eb hn (k := 1 / 2 + 24 / 100000) (a := 100024 / 100000) (by norm_num) (by norm_num)
    (by norm_num)
  have hm := ten_eb hn (k := kdot (646 / 1000) / 2 + 24 / 100000) (a := 851703 / 1000000)
    (by positivity) (by norm_num)
    (by have : 2 * ((1 / 2 + 3533 / 5000 / (314159 / 100000)) / 2 + 24 / 100000 : ℝ) ≤
            (851703 / 1000000) ^ 2 := by norm_num
        linarith)
  have hp := ten_pi hn
  have htf := ten_tauf hn
  have hp0 : 0 ≤ e4_b n 2 46 := by unfold e4_b; positivity
  have hτ := mul_le_mul htf hp hp0 (by norm_num)
  have hrr : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hrlo : 1414 / 10 ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  unfold e3_bound
  exact ten_final hrr hrlo (by positivity) hσ (by unfold e4_b; positivity) hl
    (by unfold e4_b; positivity) hm hp0 hp (by positivity) hτ (by norm_num)

end BstLean.Part183.T

open BstLean.Part183.T in
#print axioms ten_kE
open BstLean.Part183.T in
#print axioms ten_side
open BstLean.Part183.T in
#print axioms ten_eta
