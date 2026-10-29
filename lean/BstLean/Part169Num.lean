import BstLean.Part169Var
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part 169 (file `Num`): the numerical condition `P_B ≤ 0.004295²` for every `n ≥ 80 000`

No proof is left open; no `native_decide` or `axiom` is used.

* Bounds of the constants for `n ≥ 80 000` (`r = √n ≥ 282`): `HfN ≤ 4.03`, `σ₀ ≤ 2.03/√n`,
  `c1F ≤ 0.19`, `c2F ≤ 0.09`, `J_z ≥ 0.99 n√n`, `√qB ≥ 0.655`, `g_f ≤ 0.0002`,
  `r_f ≤ 0.0014`, `g_ω ≤ 0.0016`, `r_ω ≤ 0.0014`, `v_max ≤ 0.00041`, `C_v ≤ 0.00005`,
  `χ_A⁺ ≤ 1.025`.
* **`PB_le`**: with `ε = 1/50`, if `A_ω + 8.06A_f ≤ 0.72` then
  `P_B ≤ 0.004295²` (the margin is about 2.6% at `n = 80 000`).
* **`classifier_paper_A80k`**: the end theorem where the numerical condition is the linear
  condition `A_ω + 8.06A_f ≤ 0.72` on the two exact-rule allowances.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part150 (c1F c2F)
open BstLean.Part166 (goodD)

variable {n : ℕ}

lemma sqrt_n_ge (hn : 80000 ≤ n) : (282 : ℝ) ≤ √(n : ℝ) := by
  rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
  have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma n_eq_sq (n : ℕ) : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm

/-- `HfN n = 2(1 + 2/r)(2 + 5/r²)`, `r = √n`. -/
lemma HfN_eq (hn : 1 ≤ n) :
    HfN n = 2 * (√(n : ℝ) + 2) * (2 * (n : ℝ) + 5) / (√(n : ℝ) * n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hn0
  unfold HfN O1n O2n mA
  push_cast
  rw [Real.sqrt_div' _ hn0.le, Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ (n : ℝ) ^ 2),
    Real.sqrt_sq hn0.le]
  have e : (n : ℝ) = √(n : ℝ) ^ 2 := n_eq_sq n
  have h2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  rw [h2]
  nth_rewrite 1 [e]
  ring

lemma HfN_le (hn : 80000 ≤ n) : HfN n ≤ 403 / 100 := by
  have hr := sqrt_n_ge hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [HfN_eq (by omega), div_le_iff₀ (by positivity)]
  have e : (n : ℝ) = √(n : ℝ) ^ 2 := n_eq_sq n
  set r := √(n : ℝ)
  rw [e]
  nlinarith [sq_nonneg r, mul_pos (by linarith : (0:ℝ) < r) (by linarith : (0:ℝ) < r)]

lemma HfN_nonneg (hn : 1 ≤ n) : 0 ≤ HfN n := by
  have := O1n_pos (n := n) hn; have := O2n_pos (n := n) hn
  unfold HfN; positivity

/-- `sig0sq n ≤ 4.12/n`. -/
lemma sig0sq_le (hn : 80000 ≤ n) : sig0sq n ≤ 412 / 100 / n := by
  have hr := sqrt_n_ge hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  set r := √(n : ℝ) with hrdef
  have e : (n : ℝ) = r ^ 2 := n_eq_sq n
  have hr0 : 0 < r := by linarith
  have hO : O1n n ^ 2 = 2 * (r + 2) ^ 2 := by
    unfold O1n
    rw [mul_pow, Real.sq_sqrt (by positivity), ← hrdef, e]
    field_simp
  unfold sig0sq mA
  push_cast
  rw [hO]
  have key : 2 / (n : ℝ) ^ 2 * ((n : ℝ) * (2 * (r + 2) ^ 2) / ((n : ℝ) - 1)) =
      4 * (r + 2) ^ 2 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp; ring
  rw [key, div_le_div_iff₀ (by positivity) hn0, e]
  nlinarith [sq_nonneg r, mul_pos hr0 hr0, pow_pos hr0 3, pow_pos hr0 4]

/-- **The price bound from abstract bounds of its inputs** (`ε = 1/50`, `d = dStar`). -/
theorem PB_bound (hn : 80000 ≤ n) {χ vmax aw af Hf Cv : ℝ} (hχ0 : 0 ≤ χ) (hχ : χ ≤ 1025 / 1000)
    (hv : vmax ≤ 41 / 100000) (haw0 : 0 ≤ aw) (haf0 : 0 ≤ af)
    (haf : af ≤ 91 / 1000) (hHf0 : 0 ≤ Hf) (hX : aw + 2 * Hf * af ≤ 7359 / 10000)
    (hCv0 : 0 ≤ Cv) (hCv : Cv ≤ 5 / 100000) :
    PB n χ dStar (1 / 50) vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2 := by
  have hN : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hd : dStar = 9999 / 10000 * (4691 / 10000) ^ 2 := by unfold dStar; norm_num
  unfold PB
  rw [hd]
  set d : ℝ := 9999 / 10000 * (4691 / 10000) ^ 2 with hdd
  have hd0 : 0 < d := by rw [hdd]; norm_num
  have hdl : 22 / 100 ≤ d := by rw [hdd]; norm_num
  -- `T ≥ 0.0181`
  have hT : 181 / 10000 ≤ 1 / 50 - vmax / d := by
    have : vmax / d ≤ 41 / 100000 / (22 / 100) :=
      div_le_div₀ (by norm_num) hv (by norm_num) hdl
    have h2 : (41 / 100000 : ℝ) / (22 / 100) ≤ 19 / 10000 := by norm_num
    linarith
  have hT0 : 0 < 1 / 50 - vmax / d := lt_of_lt_of_le (by norm_num) hT
  -- `af²/n`
  have haf2 : af ^ 2 ≤ 8281 / 1000000 := by nlinarith
  have hafn : af ^ 2 / n ≤ 2 / 10000000 := by
    rw [div_le_iff₀ hN0]; nlinarith
  have hafn0 : 0 ≤ af ^ 2 / n := by positivity
  -- `B_S`
  have hB0 : 0 ≤ (aw + 2 * Hf * af + af ^ 2 / n + Cv) / d := by positivity
  have hB : (aw + 2 * Hf * af + af ^ 2 / n + Cv) / d ≤ 73596 / 100000 / d :=
    div_le_div_of_nonneg_right (by linarith) hd0.le
  have hB2 : ((aw + 2 * Hf * af + af ^ 2 / n + Cv) / d) ^ 2 / (8 * (1 - 1 / 50)) ≤
      (73596 / 100000 / d) ^ 2 / (8 * (1 - 1 / 50)) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ hB0 hB 2) (by norm_num)
  have hK1 : (73596 / 100000 / d) ^ 2 / (8 * (1 - 1 / 50)) ≤ 14271 / 10000 := by
    rw [hdd]; norm_num
  -- `c_f a_f²`
  have hcf : χ / (2 * (2 - 1 / 50) * d) * af ^ 2 ≤ 1025 / 1000 / (2 * (2 - 1 / 50) * d) *
      (8281 / 1000000) :=
    mul_le_mul (div_le_div_of_nonneg_right hχ (by positivity)) haf2 (sq_nonneg _) (by positivity)
  have hK2 : 1025 / 1000 / (2 * (2 - 1 / 50) * d) * (8281 / 1000000) ≤ 98 / 10000 := by
    rw [hdd]; norm_num
  have ht1 : (χ / (2 * (2 - 1 / 50) * d) * af ^ 2 + ((aw + 2 * Hf * af + af ^ 2 / n + Cv) / d) ^ 2 /
      (8 * (1 - 1 / 50))) / n ≤ (14271 / 10000 + 98 / 10000) / 80000 := by
    have hnum0 : 0 ≤ χ / (2 * (2 - 1 / 50) * d) * af ^ 2 +
        ((aw + 2 * Hf * af + af ^ 2 / n + Cv) / d) ^ 2 / (8 * (1 - 1 / 50)) := by positivity
    calc _ ≤ (14271 / 10000 + 98 / 10000) / (n : ℝ) :=
          div_le_div_of_nonneg_right (by linarith) hN0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hN
  -- the exceptional mass
  have hm1 : (aw + 2 * Hf * af) / (99 / 100 * d * n * (1 / 50 - vmax / d)) ≤ 3 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 99 / 100 * (22 / 100) * 80000 * (181 / 10000) ≤ 99 / 100 * d * n * (1 / 50 - vmax / d) := by
      have h1 : (0 : ℝ) ≤ 99 / 100 * (22 / 100) := by norm_num
      have h2 : 99 / 100 * (22 / 100) ≤ 99 / 100 * d := by linarith
      have h3 : 99 / 100 * (22 / 100) * 80000 ≤ 99 / 100 * d * n :=
        mul_le_mul h2 hN (by norm_num) (by positivity)
      exact mul_le_mul h3 hT (by norm_num) (by positivity)
    nlinarith
  have hm2 : af ^ 2 / (1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d)) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / 100 * (22 / 100) * 80000 ^ 2 * (181 / 10000) ≤
        1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d) := by
      have h2 : 1 / 100 * (22 / 100) ≤ 1 / 100 * d := by linarith
      have h3 : (1 / 100 * (22 / 100) : ℝ) * 80000 ^ 2 ≤ 1 / 100 * d * n ^ 2 :=
        mul_le_mul h2 (pow_le_pow_left₀ (by norm_num) hN 2) (by norm_num) (by positivity)
      exact mul_le_mul h3 hT (by norm_num) (by positivity)
    nlinarith
  have hm10 : 0 ≤ (aw + 2 * Hf * af) / (99 / 100 * d * n * (1 / 50 - vmax / d)) := by positivity
  have hm20 : 0 ≤ af ^ 2 / (1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d)) := by positivity
  have ht2 : 2 * (((aw + 2 * Hf * af) / (99 / 100 * d * n * (1 / 50 - vmax / d))) ^ 6 +
      (af ^ 2 / (1 / 100 * d * n ^ 2 * (1 / 50 - vmax / d))) ^ 4) ≤
      2 * ((3 / 1000) ^ 6 + (1 / 1000) ^ 4) := by
    have := pow_le_pow_left₀ hm10 hm1 6
    have := pow_le_pow_left₀ hm20 hm2 4
    linarith
  have hfin : (14271 / 10000 + 98 / 10000) / 80000 + 2 * ((3 / 1000) ^ 6 + (1 / 1000) ^ 4) ≤
      ((4295 : ℝ) / 10 ^ 6) ^ 2 := by norm_num
  linarith

/-! ## Bounds of the constants -/

lemma exp_half_le : rexp (1 / 2) ≤ 16488 / 10000 := by
  have h := Real.exp_one_lt_d9
  have e : rexp (1 / 2) ^ 2 = rexp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have h0 := Real.exp_pos (1 / 2)
  nlinarith

lemma c1F_le {J : ℕ} (hJ : 1000000 ≤ J) : c1F (rexp (1 / 2) / 12) J ≤ 19 / 100 := by
  have hJR : (1000000 : ℝ) ≤ J := by exact_mod_cast hJ
  have hpi1 : (314 / 100 : ℝ) < π := by linarith [Real.pi_gt_d2]
  have hpi2 := Real.pi_lt_d4
  have hs1 : √(π / 2) ≤ 12534 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hs2 : √(2 * π) ≤ 25067 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith
  have hsJ : 1000 ≤ √(J : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have he := exp_half_le
  have hex : rexp (-((J : ℝ) / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hex0 := Real.exp_pos (-((J : ℝ) / 2))
  unfold c1F
  have t1 : rexp (1 / 2) / 12 * √(π / 2) ≤ 16488 / 10000 / 12 * (12534 / 10000) :=
    mul_le_mul (div_le_div_of_nonneg_right he (by norm_num)) hs1 (Real.sqrt_nonneg _)
      (by norm_num)
  have t3 : 44 / 9 * (√(2 * π) / 90) / J ≤ 44 / 9 * (25067 / 10000 / 90) / 1000000 :=
    div_le_div₀ (by norm_num) (by gcongr) (by norm_num) hJR
  have t4 : rexp (-((J : ℝ) / 2)) / √(J : ℝ) ≤ 1 / 1000 :=
    div_le_div₀ (by norm_num) hex (by norm_num) hsJ
  have hin : rexp (1 / 2) / 12 * √(π / 2) + √(2 * π) / 6 + 44 / 9 * (√(2 * π) / 90) / J +
      rexp (-((J : ℝ) / 2)) / √(J : ℝ) ≤ 5911 / 10000 := by
    have : √(2 * π) / 6 ≤ 25067 / 10000 / 6 := div_le_div_of_nonneg_right hs2 (by norm_num)
    have : (16488 / 10000 / 12 * (12534 / 10000) : ℝ) + 25067 / 10000 / 6 +
        44 / 9 * (25067 / 10000 / 90) / 1000000 + 1 / 1000 ≤ 5911 / 10000 := by norm_num
    linarith
  have hin0 : 0 ≤ rexp (1 / 2) / 12 * √(π / 2) + √(2 * π) / 6 + 44 / 9 * (√(2 * π) / 90) / J +
      rexp (-((J : ℝ) / 2)) / √(J : ℝ) := by positivity
  calc 1 / π * (rexp (1 / 2) / 12 * √(π / 2) + √(2 * π) / 6 + 44 / 9 * (√(2 * π) / 90) / J +
        rexp (-((J : ℝ) / 2)) / √(J : ℝ)) ≤ 1 / (314 / 100) * (5911 / 10000) :=
        mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi1.le) hin hin0
          (by norm_num)
    _ ≤ 19 / 100 := by norm_num

lemma c2F_le {J : ℕ} (hJ : 1000000 ≤ J) : c2F (rexp (1 / 2) / 12) J ≤ 9 / 100 := by
  have hJR : (1000000 : ℝ) ≤ J := by exact_mod_cast hJ
  have hpi1 : (314 / 100 : ℝ) < π := by linarith [Real.pi_gt_d2]
  have hs2 : √(2 * π) ≤ 25067 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]; linarith [Real.pi_lt_d4]
  have hsJ : 1000 ≤ √(J : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have he := exp_half_le
  have hex : rexp (-((J : ℝ) / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpi3 : (314 / 100 : ℝ) ^ 3 ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) hpi1.le 3
  unfold c2F
  have t2 : √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) ≤
      25067 / 10000 * (56807 / (6750 * (314 / 100) ^ 3)) / 1000 := by
    apply div_le_div₀ (by positivity) _ (by norm_num) hsJ
    exact mul_le_mul hs2 (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left hpi3 (by norm_num))) (by positivity) (by norm_num)
  have t3 : rexp (-((J : ℝ) / 2)) / J ≤ 1 / 1000000 := div_le_div₀ (by norm_num) hex (by norm_num) hJR
  have hin : rexp (1 / 2) / 12 + √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) +
      rexp (-((J : ℝ) / 2)) / J ≤ 1382 / 10000 := by
    have : rexp (1 / 2) / 12 ≤ 16488 / 10000 / 12 := div_le_div_of_nonneg_right he (by norm_num)
    have : (16488 / 10000 / 12 : ℝ) + 25067 / 10000 * (56807 / (6750 * (314 / 100) ^ 3)) / 1000 +
        1 / 1000000 ≤ 1382 / 10000 := by norm_num
    linarith
  have hin0 : 0 ≤ rexp (1 / 2) / 12 + √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) +
      rexp (-((J : ℝ) / 2)) / J := by positivity
  calc 2 / π * (rexp (1 / 2) / 12 + √(2 * π) * (56807 / (6750 * π ^ 3)) / √(J : ℝ) +
        rexp (-((J : ℝ) / 2)) / J) ≤ 2 / (314 / 100) * (1382 / 10000) :=
        mul_le_mul (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpi1.le) hin hin0
          (by norm_num)
    _ ≤ 9 / 100 := by norm_num

lemma rpow_three_halves (n : ℕ) : (n : ℝ) ^ ((3 : ℝ) / 2) = n * √(n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
    Real.sqrt_eq_rpow]

/-- `J_z ≥ n√n − 1 ≥ 0.99·n√n` and `J_z ≥ 10⁶`. -/
lemma Jz_ge (hn : 80000 ≤ n) : 99 / 100 * ((n : ℝ) * √(n : ℝ)) ≤ Jz n ∧ 1000000 ≤ Jz n := by
  have hr := sqrt_n_ge hn
  have hN : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (n : ℝ) * √(n : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    rw [← rpow_three_halves]; exact Nat.le_ceil _
  have hbig : (22560000 : ℝ) ≤ (n : ℝ) * √(n : ℝ) := by nlinarith
  have hc1 : 1 ≤ ⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have : (1 : ℝ) ≤ (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have hJ : (Jz n : ℝ) = (⌈(n : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz; rw [Nat.cast_sub hc1]; simp
  constructor
  · rw [hJ]; nlinarith
  · have : (1000000 : ℝ) ≤ Jz n := by rw [hJ]; linarith
    exact_mod_cast this

lemma sqrt_qB_ge (hn : 80000 ≤ n) : 655 / 1000 ≤ √(qB n) := by
  rw [Real.le_sqrt (by norm_num) (by linarith [qB_pos hn])]
  linarith [qB_pos hn]

lemma sqrt_sig0_le (hn : 80000 ≤ n) : √(sig0sq n) ≤ 203 / 100 / √(n : ℝ) := by
  have hr := sqrt_n_ge hn
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt hN0.le]
  refine (sig0sq_le hn).trans (div_le_div_of_nonneg_right (by norm_num) hN0.le)

lemma nDelta_le (hn : 80000 ≤ n) : (n : ℝ) * DeltaP n ≤ 12 * (7417 / 10000) / (512 * 282) := by
  have hr := sqrt_n_ge hn
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold DeltaP
  rw [Real.sqrt_div' _ hN0.le]
  have hs : √(55 / 100 : ℝ) ≤ 7417 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have e : (n : ℝ) * (12 * (√(55 / 100) / √(n : ℝ)) / (512 * n)) = 12 * √(55 / 100) / (512 * √(n : ℝ)) := by
    field_simp
  rw [e]
  exact div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)

lemma O2O1_eq (hn : 1 ≤ n) : O2n n * O1n n = HfN n * √(n : ℝ) := by
  have hr : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  unfold HfN; field_simp

lemma gf_le (hn : 80000 ≤ n) :
    (n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) ≤ 2 / 10000 := by
  have hr := sqrt_n_ge hn
  have hq := sqrt_qB_ge hn
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) (by omega)
  have hD := nDelta_le hn
  have hD0 : 0 ≤ (n : ℝ) * DeltaP n := by unfold DeltaP; positivity
  rw [O2O1_eq (by omega)]
  have e : (n : ℝ) * (HfN n * √(n : ℝ) * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) =
      HfN n * ((n : ℝ) * DeltaP n) / (2 * √(qB n)) := by
    field_simp
  rw [e]
  calc HfN n * ((n : ℝ) * DeltaP n) / (2 * √(qB n))
      ≤ 403 / 100 * (12 * (7417 / 10000) / (512 * 282)) / (2 * (655 / 1000)) :=
        div_le_div₀ (by positivity) (mul_le_mul hH hD hD0 (by norm_num)) (by norm_num)
          (by linarith)
    _ ≤ 2 / 10000 := by norm_num

lemma gw_le (hn : 80000 ≤ n) :
    (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) ≤ 16 / 10000 := by
  have hr := sqrt_n_ge hn
  have hq := sqrt_qB_ge hn
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) (by omega)
  have hD := nDelta_le hn
  have hD0 : 0 ≤ (n : ℝ) * DeltaP n := by unfold DeltaP; positivity
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [O2O1_eq (by omega)]
  have e : (n : ℝ) * (2 * (HfN n * √(n : ℝ)) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) =
      HfN n ^ 2 * ((n : ℝ) * DeltaP n) / √(qB n) := by
    rw [mul_pow, Real.sq_sqrt hN0.le]; field_simp
  rw [e]
  have hH2 : HfN n ^ 2 ≤ (403 / 100) ^ 2 := pow_le_pow_left₀ hH0 hH 2
  calc HfN n ^ 2 * ((n : ℝ) * DeltaP n) / √(qB n)
      ≤ (403 / 100) ^ 2 * (12 * (7417 / 10000) / (512 * 282)) / (655 / 1000) :=
        div_le_div₀ (by positivity) (mul_le_mul hH2 hD hD0 (by norm_num)) (by norm_num) hq
    _ ≤ 16 / 10000 := by norm_num

lemma rf_le (hn : 80000 ≤ n) :
    (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) / Jz n)) ≤ 14 / 10000 := by
  have hr := sqrt_n_ge hn
  obtain ⟨hJ, hJ6⟩ := Jz_ge hn
  have hc := c1F_le hJ6
  have hc0 := c1F_nonneg (Jz n)
  have hs := sqrt_sig0_le hn
  have hs0 := Real.sqrt_nonneg (sig0sq n)
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr0 : 0 < √(n : ℝ) := by linarith
  have hJ0 : (0 : ℝ) < Jz n := lt_of_lt_of_le (by positivity) hJ
  have e : (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) / Jz n)) =
      ((n : ℝ) * √(n : ℝ)) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n)) / Jz n := by ring
  rw [e, div_le_iff₀ hJ0]
  have h1 : c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) ≤ 19 / 100 * (203 / 100 / √(n : ℝ)) :=
    mul_le_mul hc hs hs0 (by norm_num)
  have h2 : ((n : ℝ) * √(n : ℝ)) * (19 / 100 * (203 / 100 / √(n : ℝ))) =
      19 / 100 * (203 / 100) * n := by field_simp
  have h3 : 19 / 100 * (203 / 100) * (n : ℝ) ≤ 14 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := by
    nlinarith
  calc ((n : ℝ) * √(n : ℝ)) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n))
      ≤ ((n : ℝ) * √(n : ℝ)) * (19 / 100 * (203 / 100 / √(n : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 19 / 100 * (203 / 100) * n := h2
    _ ≤ 14 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := h3
    _ ≤ 14 / 10000 * Jz n := mul_le_mul_of_nonneg_left hJ (by norm_num)

lemma rw_le (hn : 80000 ≤ n) :
    (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) ^ 2 / Jz n)) ≤ 14 / 10000 := by
  have hr := sqrt_n_ge hn
  obtain ⟨hJ, hJ6⟩ := Jz_ge hn
  have hc := c2F_le hJ6
  have hc0 := c2F_nonneg (Jz n)
  have hs := sig0sq_le hn
  have hs0 := (sig0sq_pos (n := n) (by omega)).le
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hr0 : 0 < √(n : ℝ) := by linarith
  have hJ0 : (0 : ℝ) < Jz n := lt_of_lt_of_le (by positivity) hJ
  rw [Real.sq_sqrt hs0]
  have e : (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n / Jz n)) =
      ((n : ℝ) * n) * (c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n) / Jz n := by ring
  rw [e, div_le_iff₀ hJ0]
  have h1 : c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n ≤ 9 / 100 * (412 / 100 / n) :=
    mul_le_mul hc hs hs0 (by norm_num)
  have h2 : ((n : ℝ) * n) * (9 / 100 * (412 / 100 / n)) = 9 / 100 * (412 / 100) * n := by
    field_simp
  have h3 : 9 / 100 * (412 / 100) * (n : ℝ) ≤ 14 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := by
    nlinarith
  calc ((n : ℝ) * n) * (c2F (rexp (1 / 2) / 12) (Jz n) * sig0sq n)
      ≤ ((n : ℝ) * n) * (9 / 100 * (412 / 100 / n)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 9 / 100 * (412 / 100) * n := h2
    _ ≤ 14 / 10000 * (99 / 100 * ((n : ℝ) * √(n : ℝ))) := h3
    _ ≤ 14 / 10000 * Jz n := mul_le_mul_of_nonneg_left hJ (by norm_num)

lemma vmaxN_le (hn : 80000 ≤ n) : vmaxN n ≤ 41 / 100000 := by
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) (by omega)
  have hN : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold vmaxN
  rw [← HfN]
  rw [div_le_iff₀ (by linarith)]
  have : HfN n ^ 2 ≤ (403 / 100) ^ 2 := pow_le_pow_left₀ hH0 hH 2
  nlinarith

lemma CvN_le (hn : 80000 ≤ n) : CvN n ≤ 5 / 100000 := by
  have hN : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold CvN
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma chi_le (hn : 80000 ≤ n) : BstLean.Part164.chiUp n / n ≤ 1025 / 1000 := by
  have hr := sqrt_n_ge hn
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold BstLean.Part164.chiUp
  rw [div_le_iff₀ hN0, Real.sqrt_mul' _ (by norm_num : (0:ℝ) ≤ 12)]
  have h12 : √(12 : ℝ) ≤ 34642 / 10000 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have e : (n : ℝ) = √(n : ℝ) ^ 2 := n_eq_sq n
  nlinarith [mul_le_mul_of_nonneg_left h12 (by linarith : (0:ℝ) ≤ √(n : ℝ))]

/-- **The numerical condition**: `A_ω + 8.06A_f ≤ 0.72` gives `P_B ≤ 0.004295²` (`ε = 1/50`). -/
theorem PB_le (hn : 80000 ≤ n) {Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw)
    (hA : Aw + 806 / 100 * Af ≤ 72 / 100) :
    PB n (BstLean.Part164.chiUp n / n) dStar (1 / 50) (vmaxN n) (aWn n Aw √(sig0sq n))
      (aFn n Af √(sig0sq n)) (HfN n) (CvN n) ≤ (4295 / 10 ^ 6) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN0 : (0 : ℝ) < n := by
    have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨hJ, -⟩ := Jz_ge hn
  have hJ0 : (0 : ℝ) < Jz n := lt_of_lt_of_le (by positivity) hJ
  have hq0 : 0 < √(qB n) := lt_of_lt_of_le (by norm_num) (sqrt_qB_ge hn)
  have hO1 := O1n_pos (n := n) hn1
  have hO2 := O2n_pos (n := n) hn1
  have hDP : 0 ≤ DeltaP n := by unfold DeltaP; positivity
  have hc1 := c1F_nonneg (Jz n)
  have hc2 := c2F_nonneg (Jz n)
  have g1 := gf_le hn
  have g2 := rf_le hn
  have g3 := gw_le hn
  have g4 := rw_le hn
  have g10 : 0 ≤ (n : ℝ) * (O2n n * O1n n * (DeltaP n / 2) / (√(n : ℝ) * √(qB n))) := by
    positivity
  have g20 : 0 ≤ (n : ℝ) * (√(n : ℝ) * (c1F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) / Jz n)) := by
    positivity
  have g30 : 0 ≤ (n : ℝ) * (2 * (O2n n * O1n n) ^ 2 * (DeltaP n / 2) / (n * √(qB n))) := by
    positivity
  have g40 : 0 ≤ (n : ℝ) * (n * (c2F (rexp (1 / 2) / 12) (Jz n) * √(sig0sq n) ^ 2 / Jz n)) := by
    positivity
  have haf : aFn n Af √(sig0sq n) ≤ Af + 16 / 10000 := by unfold aFn; linarith
  have haf0 : 0 ≤ aFn n Af √(sig0sq n) := by unfold aFn; linarith
  have haw : aWn n Aw √(sig0sq n) ≤ Aw + 3 / 1000 := by unfold aWn; linarith
  have haw0 : 0 ≤ aWn n Aw √(sig0sq n) := by unfold aWn; linarith
  have hH := HfN_le hn
  have hH0 := HfN_nonneg (n := n) hn1
  have hCv0 : 0 ≤ CvN n := by
    have : (0 : ℝ) < (n : ℝ) - 2 := by
      have : (80000 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    unfold CvN; positivity
  refine PB_bound hn (by unfold BstLean.Part164.chiUp; positivity) (chi_le hn) (vmaxN_le hn)
    haw0 haf0 (by linarith) hH0 ?_ hCv0 (CvN_le hn)
  have h1 : 2 * HfN n * aFn n Af √(sig0sq n) ≤ 2 * (403 / 100) * aFn n Af √(sig0sq n) :=
    mul_le_mul_of_nonneg_right (by linarith) haf0
  nlinarith

/-- **The classifier theorem with `BIAS_hyp` reduced to two exact-rule `L⁸` allowances under a
linear condition** (every `n ≥ 80 000`). Remaining: `MomZ c A_f A_ω` on
`goodD n D (E_A ∩ E_bias)` with `A_ω + 8.06A_f ≤ 0.72`, and the charges `δ_A + δ_bias ≤ roomE`. -/
theorem classifier_paper_A80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    {Af Aw : ℝ} (hAf : 0 < Af) (hAw : 0 < Aw) (hlin : Aw + 806 / 100 * Af ≤ 72 / 100)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomZ c Af Aw) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hT : 0 < 1 / 50 - vmaxN n / dStar := by
    have hv := vmaxN_le hn
    have hd : (22 : ℝ) / 100 ≤ dStar := by unfold dStar; norm_num
    have : vmaxN n / dStar ≤ 41 / 100000 / (22 / 100) :=
      div_le_div₀ (by norm_num) hv (by norm_num) hd
    have h2 : (41 / 100000 : ℝ) / (22 / 100) < 1 / 50 := by norm_num
    linarith
  exact classifier_paper_exact80k hn t hEA hEb hA hb hroom (by norm_num) hT hAf hAw
    (PB_le hn hAf hAw hlin) hM

end BstLean.Part169
