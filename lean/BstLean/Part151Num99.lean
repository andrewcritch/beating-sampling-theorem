import BstLean.Part151VA2
import BstLean.Part139Scale

/-!
# Part 151: a numeric corollary of the frame: success `≥ 99/100` for every `n ≥ 16 384`, IF the
`A`-stage bounds hold with the constants of the document

Role: `delegations/statements/p151-spec.md`, items 3 and 5. This file evaluates
`theorem5_frameProg` (`Part151VA2`) at `δ = 6/100`, `L_c = 12`, `u_F = 5`, `ε_W = 26/100`,
`θ = 38/100`, with the hypotheses `‖C_r‖_op ≤ 1.662·γ_A/n`, `n·Dv ≤ 4.193` and
`Pr(X12ᶜ) ≤ 27/10000`.

* `two_PhiBar_seven_half`: `2Φ̄(a) ≤ 5/10000` for `a ≥ 7/2`.
* `exp_neg_twelve`: `e^{−12} ≤ 62/10⁷`.
* `deltaC_le`, `lF_le`, `chF_le`: the constants for `n ≥ 16 384`.
* **`vbar_num`**: `c_V = vbar·n²/4 ≤ 6.14` for every `n ≥ 16 384`, `k ≥ 100n`.
* **`theorem5_cond_99`**: the straight-line program `fullProg150 k n J` succeeds with
  probability at least `99/100`, under the hypotheses on the set `X12` of `(W, (A₁, A₂))`.
* `theorem5_cond_99_samp`: the same for `gSampH bh k` with any measurable centre.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part141 (tauWA)
open BstLean.Part149 (thA tauOutOf)
open BstLean.Part150 (CMap gSampH bTW measurable_bTW fullProg150 fullVal)

/-! ## Two numbers -/

/-- `2Φ̄(a) ≤ 5/10000` for `a ≥ 7/2`. -/
theorem two_PhiBar_seven_half {a : ℝ} (ha : 7 / 2 ≤ a) : 2 * PhiBar a ≤ 5 / 10000 := by
  have hanti : PhiBar a ≤ PhiBar (7 / 2) := tail_anti ha
  have h := tail_le_mills3 (a := 7 / 2) (by norm_num)
  rw [pdf_eq] at h
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h9 : Real.exp (49 / 8) ^ 8 = Real.exp 1 ^ 49 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have hp : (2.718 : ℝ) ^ 49 ≤ Real.exp 1 ^ 49 := pow_le_pow_left₀ (by norm_num) he.le 49
  have hE : (429 : ℝ) ≤ Real.exp (49 / 8) := by
    have hpos := Real.exp_pos (49 / 8 : ℝ)
    by_contra hc
    rw [not_le] at hc
    have : Real.exp (49 / 8) ^ 8 < 429 ^ 8 := pow_lt_pow_left₀ hc hpos.le (by norm_num)
    rw [h9] at this
    have h2 : (429 : ℝ) ^ 8 ≤ (2.718 : ℝ) ^ 49 := by norm_num
    linarith
  have hx : Real.exp (-((7 / 2 : ℝ) ^ 2 / 2)) ≤ 1 / 429 := by
    rw [show -((7 / 2 : ℝ) ^ 2 / 2) = -(49 / 8) by norm_num, Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hE
  have hs := sqrt_two_pi_ge
  have hsi : (√(2 * Real.pi))⁻¹ ≤ 2 / 5 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; convert hs using 1; norm_num
  have hprod : (√(2 * Real.pi))⁻¹ * Real.exp (-((7 / 2 : ℝ) ^ 2 / 2)) ≤ 2 / 5 * (1 / 429) :=
    mul_le_mul hsi hx (Real.exp_pos _).le (by norm_num)
  have hq : (0 : ℝ) ≤ 1 / (7 / 2) - 1 / (7 / 2) ^ 3 + 3 / (7 / 2) ^ 5 := by norm_num
  have h3 := mul_le_mul_of_nonneg_right hprod hq
  have h4 : (2 / 5 * (1 / 429) : ℝ) * (1 / (7 / 2) - 1 / (7 / 2) ^ 3 + 3 / (7 / 2) ^ 5) ≤
      5 / 20000 := by norm_num
  have h5 : PhiBar (7 / 2) ≤ 5 / 20000 := by
    unfold PhiBar
    linarith
  linarith

/-- `e^{−12} ≤ 62/10⁷`. -/
lemma exp_neg_twelve : Real.exp (-12) ≤ 62 / 10000000 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h12 : Real.exp 12 = Real.exp 1 ^ 12 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.718 : ℝ) ^ 12 ≤ Real.exp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) he.le 12
  have hE : (162552 : ℝ) ≤ Real.exp 12 := by
    rw [h12]
    refine le_trans ?_ hp
    norm_num
  rw [Real.exp_neg, inv_eq_one_div]
  refine (one_div_le_one_div_of_le (by norm_num) hE).trans ?_
  norm_num

variable {k n : ℕ}

/-! ## The constants for `n ≥ 16 384` -/

lemma mF_ge_128 (hn : 16384 ≤ n) : 128 * (n : ℝ) ≤ mF n := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  have h := BstLean.Part139.mF_ge_s (n := n) (by omega)
  nlinarith

lemma mF_ge_big (hn : 16384 ≤ n) : (2097152 : ℝ) ≤ mF n := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have := mF_ge_128 hn
  linarith

lemma deltaC_le (hn : 16384 ≤ n) : deltaC n 12 ≤ 557 / 10000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h1 : (12 : ℝ) / n ≤ 12 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h2 : √((12 : ℝ) / n) ≤ 271 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    refine h1.trans ?_
    norm_num
  have h3 : 2 * (12 : ℝ) / n ≤ 2 * 12 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold deltaC
  have h4 : (2 * 12 / 16384 : ℝ) ≤ 15 / 10000 := by norm_num
  linarith

lemma deltaC_nn (n : ℕ) : 0 ≤ deltaC n 12 := deltaC_nonneg n (by norm_num)

/-- `t_F·L_F² ≤ 38.304/n` (`l_F ≤ 1.197` at `u_F = 5`). -/
lemma tLF_le (hn : 16384 ≤ n) :
    2 / (mF n : ℝ) * LFc n 5 ^ 2 ≤ 38304 / 1000 / (n : ℝ) ∧
      0 ≤ 2 / (mF n : ℝ) * LFc n 5 ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mF_ge_128 hn
  have hmb := mF_ge_big hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hm1 : 1 ≤ mF n := by
    have : (1 : ℝ) ≤ mF n := by linarith
    exact_mod_cast this
  set sm : ℝ := √(mF n : ℝ) with hsm
  have hsm2 : sm ^ 2 = mF n := Real.sq_sqrt hm0.le
  have hsm1 : (1448 : ℝ) ≤ sm := by
    have h2 : (1448 : ℝ) ^ 2 = 2096704 := by norm_num
    rw [hsm]
    refine Real.le_sqrt_of_sq_le ?_
    rw [h2]; linarith
  have hsm0 : 0 < sm := by linarith
  have hsn : √(n : ℝ) ≤ 884 / 10000 * sm := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, hsm2]
    nlinarith
  have hsn0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have e := tF_LF_sq hn1 hm1 5
  have e' : 2 / (mF n : ℝ) * LFc n 5 ^ 2 =
      32 / (n : ℝ) * ((1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2) := by
    unfold LFc; exact e
  rw [e']
  have p1 : 1 + 5 / (2 * sm) ≤ 1 + 5 / 2896 := by
    have : 5 / (2 * sm) ≤ 5 / 2896 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have p10 : 0 ≤ 1 + 5 / (2 * sm) := by positivity
  have q1 : 1 + (√(n : ℝ) + 5) / sm ≤ 1 + 884 / 10000 + 5 / 1448 := by
    have h1 : (√(n : ℝ) + 5) / sm = √(n : ℝ) / sm + 5 / sm := by ring
    have h2 : √(n : ℝ) / sm ≤ 884 / 10000 := by
      rw [div_le_iff₀ hsm0]; exact hsn
    have h3 : 5 / sm ≤ 5 / 1448 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsm1
    rw [h1]; linarith
  have q10 : 0 ≤ 1 + (√(n : ℝ) + 5) / sm := by positivity
  have hl : (1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2 ≤ 1197 / 1000 := by
    calc (1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2
        ≤ (1 + 5 / 2896 : ℝ) ^ 2 * (1 + 884 / 10000 + 5 / 1448) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ p10 p1 2) (pow_le_pow_left₀ q10 q1 2) (by positivity)
            (by norm_num)
      _ ≤ 1197 / 1000 := by norm_num
  constructor
  · calc 32 / (n : ℝ) * ((1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2)
        ≤ 32 / (n : ℝ) * (1197 / 1000) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = 38304 / 1000 / (n : ℝ) := by ring
  · positivity

lemma chF_le (hn : 16384 ≤ n) : chF n (6 / 100) ≤ 152 / 10000000 := by
  have hmb := mF_ge_big hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  unfold chF
  have h1 : 432 / (mF n : ℝ) ^ 2 ≤ 432 / 2097152 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hmb 2)
  have h2 : 1 + 63 / (mF n : ℝ) ≤ 1 + 63 / 2097152 := by
    have : 63 / (mF n : ℝ) ≤ 63 / 2097152 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmb
    linarith
  calc 432 / (mF n : ℝ) ^ 2 * (1 + 63 / (mF n : ℝ)) * (1 / (6 / 100 : ℝ) ^ 4 + 1 / (6 / 100) ^ 4)
      ≤ 432 / 2097152 ^ 2 * (1 + 63 / 2097152) * (1 / (6 / 100 : ℝ) ^ 4 + 1 / (6 / 100) ^ 4) := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        exact mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ ≤ 152 / 10000000 := by norm_num

/-! ## The pieces of `vbar` -/

section pieces

variable (hn : 16384 ≤ n)
include hn

lemma tauM_le :
    tauM n (6 / 100) ((1 + deltaC n 12) * (4193 / 1000 / (n : ℝ))) ≤ 3154 / 1000 / (n : ℝ) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hd := deltaC_le hn
  have hd0 := deltaC_nn n
  set dc := deltaC n 12
  unfold tauM
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have e : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * ((1 + dc) * (4193 / 1000 / n))) *
      (n : ℝ) ^ 2 = (1 + 6 / 100) * (1 + 6 / 100) * 2 * (4193 / 1000) * (1 + dc) := by
    field_simp
  rw [e]
  nlinarith

lemma tauS1_le (hk : 100 * n ≤ k) :
    √((1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * (2 * (1 + deltaC n 12))) / k) ≤
      2179 / 10000 / (n : ℝ) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK : 100 * (n : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < k := by linarith
  have hd := deltaC_le hn
  have hd0 := deltaC_nn n
  set dc := deltaC n 12
  rw [Real.sqrt_le_left (by positivity), div_pow, div_le_div_iff₀ hK0 (by positivity)]
  have e : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * (2 * (1 + dc))) * (n : ℝ) ^ 2 =
      (1 + 6 / 100) * (1 + 6 / 100) * 4 * (1 + dc) * n := by
    field_simp
    ring
  rw [e]
  have hA : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * 4 * (1 + dc) ≤ 100 * (2179 / 10000) ^ 2 := by
    nlinarith
  calc (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * 4 * (1 + dc) * n
      ≤ 100 * (2179 / 10000) ^ 2 * n := mul_le_mul_of_nonneg_right hA hx0.le
    _ = (2179 / 10000) ^ 2 * (100 * n) := by ring
    _ ≤ (2179 / 10000) ^ 2 * k := mul_le_mul_of_nonneg_left hK (by norm_num)

lemma uS_le (hk : 100 * n ≤ k) : uS n k (LFc n 5) 12 ≤ 335 / 10000 / (n : ℝ) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK : 100 * (n : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < k := by linarith
  obtain ⟨hT, hT0⟩ := tLF_le hn
  set T := 2 / (mF n : ℝ) * LFc n 5 ^ 2
  unfold uS ellS
  rw [← Real.sqrt_mul (by norm_num), Real.sqrt_le_left (by positivity)]
  have h1 : T * (2 / (n : ℝ)) / k ≤ 38304 / 1000 / (n : ℝ) * (2 / (n : ℝ)) / (100 * n) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hT (by positivity))
      (by positivity) hK
  have h2 : (2 * 12 : ℝ) * (38304 / 1000 / (n : ℝ) * (2 / (n : ℝ)) / (100 * n)) ≤
      (335 / 10000 / (n : ℝ)) ^ 2 := by
    rw [div_pow]
    have e : (2 * 12 : ℝ) * (38304 / 1000 / (n : ℝ) * (2 / (n : ℝ)) / (100 * n)) =
        (2 * 12 * (38304 / 1000) * 2 / 100) / (n : ℝ) ^ 3 := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * 12 * (38304 / 1000) * 2 / 100 : ℝ) ≤ (335 / 10000) ^ 2 * 16384 := by norm_num
    have h3 : (2 * 12 * (38304 / 1000) * 2 / 100 : ℝ) ≤ (335 / 10000) ^ 2 * n := by nlinarith
    calc (2 * 12 * (38304 / 1000) * 2 / 100 : ℝ) * (n : ℝ) ^ 2
        ≤ (335 / 10000) ^ 2 * n * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (335 / 10000) ^ 2 * (n : ℝ) ^ 3 := by ring
  have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2 * 12)
  linarith

lemma uU_le : uU n (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12 ≤ 4319 / 10000 / (n : ℝ) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hT, hT0⟩ := tLF_le hn
  set T := 2 / (mF n : ℝ) * LFc n 5 ^ 2
  unfold uU ellU
  rw [← Real.sqrt_mul (by norm_num), Real.sqrt_le_left (by positivity)]
  have h1 : T * (1662 / 1000 * (2 / (n : ℝ)) / n) ≤
      38304 / 1000 / (n : ℝ) * (1662 / 1000 * (2 / (n : ℝ)) / n) :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have h2 : (2 * 12 : ℝ) * (38304 / 1000 / (n : ℝ) * (1662 / 1000 * (2 / (n : ℝ)) / n)) ≤
      (4319 / 10000 / (n : ℝ)) ^ 2 := by
    rw [div_pow]
    have e : (2 * 12 : ℝ) * (38304 / 1000 / (n : ℝ) * (1662 / 1000 * (2 / (n : ℝ)) / n)) =
        (2 * 12 * (38304 / 1000) * (1662 / 1000) * 2) / (n : ℝ) ^ 3 := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * 12 * (38304 / 1000) * (1662 / 1000) * 2 : ℝ) ≤ (4319 / 10000) ^ 2 * 16384 := by
      norm_num
    have h3 : (2 * 12 * (38304 / 1000) * (1662 / 1000) * 2 : ℝ) ≤ (4319 / 10000) ^ 2 * n := by
      nlinarith
    calc (2 * 12 * (38304 / 1000) * (1662 / 1000) * 2 : ℝ) * (n : ℝ) ^ 2
        ≤ (4319 / 10000) ^ 2 * n * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (4319 / 10000) ^ 2 * (n : ℝ) ^ 3 := by ring
  have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2 * 12)
  linarith

lemma tauU1_le :
    √(1662 / 1000 * (2 / (n : ℝ)) / n * (2 * (1 + 6 / 100) * (1 + 6 / 100))) ≤
      27331 / 10000 / (n : ℝ) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have e : (1662 / 1000 * (2 / (n : ℝ)) / n * (2 * (1 + 6 / 100) * (1 + 6 / 100))) * (n : ℝ) ^ 2 =
      1662 / 1000 * 2 * (2 * (1 + 6 / 100) * (1 + 6 / 100)) := by
    field_simp
  rw [e]
  norm_num

/-- **The variance coefficient**: `c_V = vbar·n²/4 ≤ 6.14` for every `n ≥ 16 384`, `k ≥ 100n`,
at `δ = 6/100`, `L_c = 12`, `u_F = 5`, `M_r = 1.662·(2/n)/n`, `D̄_v = 4.193/n`. -/
theorem vbar_num (hk : 100 * n ≤ k) :
    vbar n k (6 / 100) ((1 + deltaC n 12) * (4193 / 1000 / (n : ℝ))) (2 * (1 + deltaC n 12))
      (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12 * (n : ℝ) ^ 2 / 4 ≤ 614 / 100 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hM := tauM_le hn
  have hS1 := tauS1_le hn hk
  have hS2 := uS_le hn hk
  have hU1 := tauU1_le hn
  have hU2 := uU_le hn
  set tM := tauM n (6 / 100) ((1 + deltaC n 12) * (4193 / 1000 / (n : ℝ))) with htM
  set uu := uU n (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12 with huu
  set us := uS n k (LFc n 5) 12 with hus
  have hM0 : 0 ≤ tM := by rw [htM]; unfold tauM; exact Real.sqrt_nonneg _
  have hu0 : 0 ≤ uu := uU_nonneg _ _ _ _
  have hs0 : 0 ≤ us := uS_nonneg _ _ _ _
  have hS : tauS n k (6 / 100) (2 * (1 + deltaC n 12)) (LFc n 5) 12 ≤ 2514 / 10000 / (n : ℝ) := by
    unfold tauS
    have : (2179 / 10000 / (n : ℝ)) + 335 / 10000 / n = 2514 / 10000 / n := by ring
    linarith
  have hS0 : 0 ≤ tauS n k (6 / 100) (2 * (1 + deltaC n 12)) (LFc n 5) 12 := by
    unfold tauS
    exact add_nonneg (Real.sqrt_nonneg _) hs0
  have hU : tauU n (6 / 100) (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12 ≤
      3165 / 1000 / (n : ℝ) := by
    unfold tauU
    have : (27331 / 10000 / (n : ℝ)) + 4319 / 10000 / n = 3165 / 1000 / n := by ring
    linarith
  have hU0 : 0 ≤ tauU n (6 / 100) (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12 := by
    unfold tauU
    exact add_nonneg (Real.sqrt_nonneg _) hu0
  unfold vbar
  set tS := tauS n k (6 / 100) (2 * (1 + deltaC n 12)) (LFc n 5) 12
  set tU := tauU n (6 / 100) (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12
  have a1 : tU ^ 2 ≤ (3165 / 1000 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hU0 hU 2
  have hSM : tS + tM ≤ 34054 / 10000 / (n : ℝ) := by
    have : (2514 / 10000 / (n : ℝ)) + 3154 / 1000 / n = 34054 / 10000 / n := by ring
    linarith
  have hSM0 : 0 ≤ tS + tM := add_nonneg hS0 hM0
  have a2 : (tS + tM) ^ 2 ≤ (34054 / 10000 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hSM0 hSM 2
  have a3 : (tS + tM) * uu ≤ 34054 / 10000 / (n : ℝ) * (4319 / 10000 / n) :=
    mul_le_mul hSM hU2 hu0 (by positivity)
  have e : ((3165 / 1000 / (n : ℝ)) ^ 2 + (34054 / 10000 / (n : ℝ)) ^ 2 +
      2 * (34054 / 10000 / (n : ℝ) * (4319 / 10000 / n))) * (n : ℝ) ^ 2 / 4 =
      ((3165 / 1000) ^ 2 + (34054 / 10000) ^ 2 + 2 * (34054 / 10000 * (4319 / 10000))) / 4 := by
    field_simp
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by positivity
  have h5 : tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu ≤
      (3165 / 1000 / (n : ℝ)) ^ 2 + (34054 / 10000 / (n : ℝ)) ^ 2 +
        2 * (34054 / 10000 / (n : ℝ) * (4319 / 10000 / n)) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hn2
  have h7 : (((3165 / 1000 : ℝ)) ^ 2 + (34054 / 10000) ^ 2 +
      2 * (34054 / 10000 * (4319 / 10000))) / 4 ≤ 614 / 100 := by norm_num
  have e2 : (tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu) * (n : ℝ) ^ 2 / 4 =
      (tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu) * ((n : ℝ) ^ 2 / 4) := by ring
  have e3 : ((3165 / 1000 / (n : ℝ)) ^ 2 + (34054 / 10000 / (n : ℝ)) ^ 2 +
      2 * (34054 / 10000 / (n : ℝ) * (4319 / 10000 / n))) * ((n : ℝ) ^ 2 / 4) =
      ((3165 / 1000 / (n : ℝ)) ^ 2 + (34054 / 10000 / (n : ℝ)) ^ 2 +
      2 * (34054 / 10000 / (n : ℝ) * (4319 / 10000 / n))) * (n : ℝ) ^ 2 / 4 := by ring
  rw [e2]
  rw [e3, e] at h6
  linarith

/-- The sum of all charges is at most `1/100`. -/
lemma total_le {cV : ℝ} (hcV0 : 0 < cV) (hcV : cV ≤ 614 / 100) :
    1 / (n : ℝ) + 4849 / 20000 / ((26 / 100 : ℝ) ^ 2 * (38 / 100 * (222757 / 1000000))) / n +
        (27 / 10000 + Real.exp (-12) + 2 * Real.exp (-(5 : ℝ) ^ 2 / 2) + 3 * chF n (6 / 100) +
          3 * Real.exp (-12)) +
        2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 38 / 100) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - 26 / 100) * √(n * (38 / 100 * (222757 / 1000000)) / cV)) ≤
      1 / 100 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have t1 : 1 / (n : ℝ) ≤ 1 / 16384 := one_div_le_one_div_of_le (by norm_num) hx
  have t2 : 4849 / 20000 / ((26 / 100 : ℝ) ^ 2 * (38 / 100 * (222757 / 1000000))) / n ≤
      4849 / 20000 / ((26 / 100 : ℝ) ^ 2 * (38 / 100 * (222757 / 1000000))) / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t3 : 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 38 / 100) * (222757 / 1000000)) ^ 2 / n ≤
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 38 / 100) * (222757 / 1000000)) ^ 2 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t4 := exp_neg_twelve
  have t5 : Real.exp (-(5 : ℝ) ^ 2 / 2) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by norm_num)
  have t6 := chF_le hn
  have t7 : 2 * PhiBar ((1 / 2 - 26 / 100) *
      √(n * (38 / 100 * (222757 / 1000000)) / cV)) ≤ 5 / 10000 := by
    refine two_PhiBar_seven_half ?_
    have h1 : (175 / 12 : ℝ) ≤ √(n * (38 / 100 * (222757 / 1000000)) / cV) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hcV0]
      have : (175 / 12 : ℝ) ^ 2 * cV ≤ (175 / 12) ^ 2 * (614 / 100) :=
        mul_le_mul_of_nonneg_left hcV (by norm_num)
      nlinarith
    nlinarith
  have t8 : (1 : ℝ) / 16384 +
      4849 / 20000 / ((26 / 100 : ℝ) ^ 2 * (38 / 100 * (222757 / 1000000))) / 16384 +
      (27 / 10000 + 62 / 10000000 + 2 * (62 / 10000000) + 3 * (152 / 10000000) +
        3 * (62 / 10000000)) +
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 38 / 100) * (222757 / 1000000)) ^ 2 / 16384 +
      5 / 10000 ≤ 1 / 100 := by norm_num
  linarith

end pieces

/-! ## The conditional theorems at the level `99/100` -/

/-- **The frame of Theorem 5 at the level `99/100`, for every `n ≥ 16 384`, `k ≥ 100n`, every
atom count `J`**: if there is a measurable set `X12` of values of `(W, (A₁, A₂))` with
`Pr(X12ᶜ) ≤ 27/10000` on which the centre `b = bTW J` is not `0`, `t_A|b|² ≤ 2/n`, `τ̃₀ > 0`,
`‖C_r‖_op ≤ 1.662·γ_A/n` and `Dv ≤ 4.193/n` (`Dv = n·E|v − v_p|²`), then the straight-line
program `fullProg150 k n J` of Part 150 succeeds with probability at least `99/100`. -/
theorem theorem5_cond_99 (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ 27 / 10000)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ))
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK (bTW J) W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n))
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ 4193 / 1000 / (n : ℝ)) :
    99 / 100 ≤ (jointP k n).real
      {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hMr0 : (0 : ℝ) < 1662 / 1000 * (2 / (n : ℝ)) / n := by positivity
  have h := theorem5_frameProg (k := k) (n := n) (J := J) (by omega) (by omega) h12 hp12 hb he hτ
    hMr0 hCr hDv (δ := 6 / 100) (uF := 5) (Lc := 12) (by norm_num) (by norm_num) (by norm_num)
    (εW := 26 / 100) (θ := 38 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine le_trans ?_ h
  have hv := vbar_num hn hk
  have hv0 := (vbar_pos' n k (δ := 6 / 100)
    (Dbar := (1 + deltaC n 12) * (4193 / 1000 / (n : ℝ))) (Ebar := 2 * (1 + deltaC n 12))
    (LF := LFc n 5) (Lc := 12) (by norm_num) hMr0).resolve_right hx0.ne'
  have ht := total_le hn hv0 hv
  linarith

/-- The same for the estimator `gSampH bh k` with any measurable centre map `bh`. -/
theorem theorem5_cond_99_samp (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {bh : CMap n}
    (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ 27 / 10000)
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ))
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK bh W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n))
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv bh W A₁ A₂ ≤ 4193 / 1000 / (n : ℝ)) :
    99 / 100 ≤ (jointP k n).real
      {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hMr0 : (0 : ℝ) < 1662 / 1000 * (2 / (n : ℝ)) / n := by positivity
  have h := theorem5_frameA12 (k := k) (n := n) (by omega) (by omega) hbh h12 hp12 hb he
    hMr0 hCr hDv (δ := 6 / 100) (uF := 5) (Lc := 12) (by norm_num) (by norm_num) (by norm_num)
    (εW := 26 / 100) (θ := 38 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine le_trans ?_ h
  have hv := vbar_num hn hk
  have hv0 := (vbar_pos' n k (δ := 6 / 100)
    (Dbar := (1 + deltaC n 12) * (4193 / 1000 / (n : ℝ))) (Ebar := 2 * (1 + deltaC n 12))
    (LF := LFc n 5) (Lc := 12) (by norm_num) hMr0).resolve_right hx0.ne'
  have ht := total_le hn hv0 hv
  linarith

end BstLean.Part151
