import BstLean.Part151Num99
import BstLean.Part151VB

/-!
# Part 151: the level `99/100` for every `n ≥ 16 384`, with the hypotheses in the primitive
quantities of the event table of the document (set II)

Role: `delegations/statements/p151-spec.md`, items 3 and 5. This file evaluates
`theorem5_frameProg` (`Part151VA2`) with Lemma Cr (`CrOK_of_cov`) and Lemma V (`Dv_le_of_V`,
`Part151VB`) at the constants of the document at `n = 16 384`, rounded up:
`M_P = 1.192`, `ξ_hp = 0.470`, `ξ_∥ = 0.0274`, `n·N22 = 18.334`, `n·N24 = 24.779`, `ϑ = 0.3`,
`s_* = 0.18`.

* `DvV_core`, **`DvV_num`**: the bound of Lemma V at these constants:
  `DvV ≤ 4.196/n` for every `n ≥ 16 384` (the bracket is at most `2.098`), and `ϖ < 1`.
  (With these rounded inputs the bracket is `2.09755` at `16 384`, so the constant `4.193` of
  `theorem5_cond_99` is too small; the pieces below are proved again with `4.196`.)
* `tauM_le'`, **`vbar_num'`**: `c_V = vbar·n²/4 ≤ 6.145` with `D̄_v = 4.196/n`.
* `total_le'`: the sum of all charges is at most `1/100` for `c_V ≤ 6.145`.
* **`theorem5_cond_99_V`**: the straight-line program `fullProg150 k n J` succeeds with
  probability at least `99/100`.
* `theorem5_cond_99_V_samp`: the same for `gSampH bh k` with any measurable centre.
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

/-! ## Lemma V at the constants of the document -/

/-- The bracket of Lemma V in the variable `s = √n ≥ 128`: at most `2.098`; and `ϖ < 1`. -/
lemma DvV_core {s : ℝ} (hs : 128 ≤ s) :
    (√(kappaV (3 / 10) (24779 / 1000 / s ^ 2) * (1192 / 1000)) +
        s * rthV (3 / 10) (18334 / 1000 / s ^ 2) (24779 / 1000 / s ^ 2)) ^ 2 + 274 / 10000 +
      s ^ 2 * dfrakV (s ^ 2) (18 / 100) (1192 / 1000) (274 / 10000) (18334 / 1000 / s ^ 2) ≤
        2098 / 1000 ∧
    eDeltaV (s ^ 2) (18 / 100) (1192 / 1000) (274 / 10000) (18334 / 1000 / s ^ 2) / (18 / 100) <
      1 := by
  have hs0 : 0 < s := by linarith
  have hs2 : (16384 : ℝ) ≤ s ^ 2 := by nlinarith
  have hs3 : (128 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  set N22 : ℝ := 18334 / 1000 / s ^ 2 with h22
  set N24 : ℝ := 24779 / 1000 / s ^ 2 with h24
  have a22 : N22 ≤ 18334 / 1000 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
  have a24 : N24 ≤ 24779 / 1000 / 16384 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
  have p22 : 0 ≤ N22 := by rw [h22]; positivity
  have p24 : 0 ≤ N24 := by rw [h24]; positivity
  -- `κ_ϑ`
  have hk : kappaV (3 / 10) N24 ≤ 100467 / 100000 := by
    unfold kappaV
    have e : (1 + N24 / (1 - 3 / 10)) ^ 2 +
        661 / 100 * N24 ^ 2 / ((1 - 3 / 10) ^ 2 * (3 / 10) ^ 2) =
        1 + 20 / 7 * N24 + (100 / 49 + 661 / 100 / ((7 / 10) ^ 2 * (3 / 10) ^ 2)) * N24 ^ 2 := by
      ring
    rw [e]
    have h2 : N24 ^ 2 ≤ (24779 / 1000 / 16384) ^ 2 := pow_le_pow_left₀ p24 a24 2
    have c1 := mul_le_mul_of_nonneg_left h2
      (by norm_num : (0 : ℝ) ≤ 100 / 49 + 661 / 100 / ((7 / 10) ^ 2 * (3 / 10) ^ 2))
    have c2 : (1 : ℝ) + 20 / 7 * (24779 / 1000 / 16384) +
        (100 / 49 + 661 / 100 / ((7 / 10) ^ 2 * (3 / 10) ^ 2)) * (24779 / 1000 / 16384) ^ 2 ≤
        100467 / 100000 := by norm_num
    linarith
  have hk0 : 0 ≤ kappaV (3 / 10) N24 := by unfold kappaV; positivity
  have hsq : √(kappaV (3 / 10) N24 * (1192 / 1000)) ≤ 109434 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have c : (100467 / 100000 : ℝ) * (1192 / 1000) ≤ (109434 / 100000) ^ 2 := by norm_num
    nlinarith
  -- `√n·𝔯_ϑ`
  have e1 : s * N22 = 18334 / 1000 / s := by
    rw [h22]; field_simp
  have t1 : s * N22 ≤ 18334 / 1000 / 128 := by
    rw [e1]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have t10 : 0 ≤ s * N22 := by positivity
  have hr : s * rthV (3 / 10) N22 N24 ≤ 14975 / 100000 := by
    unfold rthV
    have e2 : s * (2 * N24 ^ 2 / (3 / 10) ^ 2) = 2 * (24779 / 1000) ^ 2 / (3 / 10) ^ 2 / s ^ 3 := by
      rw [h24]; field_simp
    have t2 : 2 * (24779 / 1000 : ℝ) ^ 2 / (3 / 10) ^ 2 / s ^ 3 ≤
        2 * (24779 / 1000) ^ 2 / (3 / 10) ^ 2 / 128 ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs3
    have c : (18334 / 1000 / 128 : ℝ) + 2 * (24779 / 1000) ^ 2 / (3 / 10) ^ 2 / 128 ^ 3 ≤
        14975 / 100000 := by norm_num
    have e3 : s * (N22 + 2 * N24 ^ 2 / (3 / 10) ^ 2) =
        s * N22 + s * (2 * N24 ^ 2 / (3 / 10) ^ 2) := by ring
    rw [e3, e2]
    linarith
  have hr0 : 0 ≤ s * rthV (3 / 10) N22 N24 := by unfold rthV; positivity
  have hA : (√(kappaV (3 / 10) N24 * (1192 / 1000)) + s * rthV (3 / 10) N22 N24) ^ 2 ≤
      154777 / 100000 := by
    have h0 : 0 ≤ √(kappaV (3 / 10) N24 * (1192 / 1000)) + s * rthV (3 / 10) N22 N24 :=
      add_nonneg (Real.sqrt_nonneg _) hr0
    have h1 : √(kappaV (3 / 10) N24 * (1192 / 1000)) + s * rthV (3 / 10) N22 N24 ≤
        109434 / 100000 + 14975 / 100000 := by linarith
    calc _ ≤ (109434 / 100000 + 14975 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ 154777 / 100000 := by norm_num
  -- `e_Δ`
  set eD : ℝ := eDeltaV (s ^ 2) (18 / 100) (1192 / 1000) (274 / 10000) N22 with heD
  have heD' : eD = N22 * (2 + N22) + (2 * (1192 / 1000) + 274 / 10000) / s ^ 2 +
      2 * √((1 - 18 / 100) * (274 / 10000) / s ^ 2) := rfl
  have hroot : √((1 - 18 / 100) * (274 / 10000) / s ^ 2) ≤ 149894 / 1000000 / s := by
    rw [Real.sqrt_le_left (by positivity), div_pow]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hroot0 : 0 ≤ √((1 - 18 / 100) * (274 / 10000) / s ^ 2) := Real.sqrt_nonneg _
  have heD0 : 0 ≤ eD := by rw [heD']; positivity
  have hq : s * eD ≤ 60526 / 100000 := by
    have t2 : s * N22 * (2 + N22) ≤ 18334 / 1000 / 128 * (2 + 18334 / 1000 / 16384) :=
      mul_le_mul t1 (by linarith) (by linarith) (by norm_num)
    have e3 : s * ((2 * (1192 / 1000) + 274 / 10000) / s ^ 2) =
        (2 * (1192 / 1000) + 274 / 10000) / s := by field_simp
    have t3 : (2 * (1192 / 1000) + 274 / 10000 : ℝ) / s ≤
        (2 * (1192 / 1000) + 274 / 10000) / 128 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have t4 : s * √((1 - 18 / 100) * (274 / 10000) / s ^ 2) ≤ 149894 / 1000000 := by
      calc s * √((1 - 18 / 100) * (274 / 10000) / s ^ 2) ≤ s * (149894 / 1000000 / s) :=
            mul_le_mul_of_nonneg_left hroot hs0.le
        _ = 149894 / 1000000 := by field_simp
    have e4 : s * eD = s * N22 * (2 + N22) + s * ((2 * (1192 / 1000) + 274 / 10000) / s ^ 2) +
        2 * (s * √((1 - 18 / 100) * (274 / 10000) / s ^ 2)) := by rw [heD']; ring
    have c : (18334 / 1000 / 128 : ℝ) * (2 + 18334 / 1000 / 16384) +
        (2 * (1192 / 1000) + 274 / 10000) / 128 + 2 * (149894 / 1000000) ≤ 60526 / 100000 := by
      norm_num
    rw [e4, e3]
    linarith
  have hq0 : 0 ≤ s * eD := by positivity
  have he0 : eD ≤ 47287 / 10000000 := by
    have h1 : eD ≤ 60526 / 100000 / s := by
      rw [le_div_iff₀ hs0]; linarith
    have h2 : (60526 / 100000 : ℝ) / s ≤ 60526 / 100000 / 128 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have h3 : (60526 / 100000 : ℝ) / 128 ≤ 47287 / 10000000 := by norm_num
    linarith
  -- `n·𝔡`
  have hd : dfrakV (s ^ 2) (18 / 100) (1192 / 1000) (274 / 10000) N22 =
      eD ^ 2 / (18 / 100 * (2 - eD / (18 / 100)) ^ 2) := rfl
  have hD : s ^ 2 * dfrakV (s ^ 2) (18 / 100) (1192 / 1000) (274 / 10000) N22 ≤
      52245 / 100000 := by
    rw [hd]
    have hb1 : 2 - (47287 / 10000000 : ℝ) / (18 / 100) ≤ 2 - eD / (18 / 100) := by
      have : eD / (18 / 100) ≤ (47287 / 10000000 : ℝ) / (18 / 100) :=
        div_le_div_of_nonneg_right he0 (by norm_num)
      linarith
    have hden : (18 / 100 : ℝ) * (2 - 47287 / 10000000 / (18 / 100)) ^ 2 ≤
        18 / 100 * (2 - eD / (18 / 100)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hb1 2) (by norm_num)
    have hden0 : (0 : ℝ) < 18 / 100 * (2 - 47287 / 10000000 / (18 / 100)) ^ 2 := by norm_num
    have e : s ^ 2 * (eD ^ 2 / (18 / 100 * (2 - eD / (18 / 100)) ^ 2)) =
        (s * eD) ^ 2 / (18 / 100 * (2 - eD / (18 / 100)) ^ 2) := by ring
    rw [e]
    have hnum : (s * eD) ^ 2 ≤ (60526 / 100000) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    calc (s * eD) ^ 2 / (18 / 100 * (2 - eD / (18 / 100)) ^ 2)
        ≤ (60526 / 100000) ^ 2 / (18 / 100 * (2 - 47287 / 10000000 / (18 / 100)) ^ 2) :=
          div_le_div₀ (by norm_num) hnum hden0 hden
      _ ≤ 52245 / 100000 := by norm_num
  constructor
  · have c : (154777 / 100000 : ℝ) + 274 / 10000 + 52245 / 100000 ≤ 2098 / 1000 := by norm_num
    linarith
  · rw [div_lt_one (by norm_num)]
    linarith

variable {k n : ℕ}

/-- **Lemma V at the constants of the document** (`ϑ = 0.3`, `s_* = 0.18`, `M_P = 1.192`,
`ξ_∥ = 0.0274`, `n·N22 = 18.334`, `n·N24 = 24.779`): `DvV ≤ 4.196/n` for every `n ≥ 16 384`,
and the condition `ϖ < 1`. -/
theorem DvV_num (hn : 16384 ≤ n) :
    DvV n (3 / 10) (18 / 100) (1192 / 1000) (274 / 10000) (18334 / 1000 / (n : ℝ))
        (24779 / 1000 / (n : ℝ)) ≤ 4196 / 1000 / (n : ℝ) ∧
    eDeltaV n (18 / 100) (1192 / 1000) (274 / 10000) (18334 / 1000 / (n : ℝ)) / (18 / 100) <
      1 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hsq : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt hx0.le).symm
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  unfold DvV
  generalize √(n : ℝ) = s at hsq hs ⊢
  rw [hsq]
  obtain ⟨h1, h2⟩ := DvV_core hs
  have hs0 : 0 < s := by linarith
  refine ⟨?_, h2⟩
  calc 2 / s ^ 2 * ((√(kappaV (3 / 10) (24779 / 1000 / s ^ 2) * (1192 / 1000)) +
          s * rthV (3 / 10) (18334 / 1000 / s ^ 2) (24779 / 1000 / s ^ 2)) ^ 2 + 274 / 10000 +
        s ^ 2 * dfrakV (s ^ 2) (18 / 100) (1192 / 1000) (274 / 10000) (18334 / 1000 / s ^ 2))
      ≤ 2 / s ^ 2 * (2098 / 1000) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 4196 / 1000 / s ^ 2 := by ring

/-! ## The variance coefficient and the total with `D̄_v = 4.196/n` -/

section pieces

variable (hn : 16384 ≤ n)
include hn

lemma tauM_le' :
    tauM n (6 / 100) ((1 + deltaC n 12) * (4196 / 1000 / (n : ℝ))) ≤ 31551 / 10000 / (n : ℝ) := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hd := deltaC_le hn
  have hd0 := deltaC_nn n
  set dc := deltaC n 12
  unfold tauM
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have e : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * ((1 + dc) * (4196 / 1000 / n))) *
      (n : ℝ) ^ 2 = (1 + 6 / 100) * (1 + 6 / 100) * 2 * (4196 / 1000) * (1 + dc) := by
    field_simp
  rw [e]
  nlinarith

/-- **The variance coefficient**: `c_V = vbar·n²/4 ≤ 6.145` for every `n ≥ 16 384`,
`k ≥ 100n`, at `δ = 6/100`, `L_c = 12`, `u_F = 5`, `M_r = 1.662·(2/n)/n`, `D̄_v = 4.196/n`. -/
theorem vbar_num' (hk : 100 * n ≤ k) :
    vbar n k (6 / 100) ((1 + deltaC n 12) * (4196 / 1000 / (n : ℝ))) (2 * (1 + deltaC n 12))
      (LFc n 5) (1662 / 1000 * (2 / (n : ℝ)) / n) 12 * (n : ℝ) ^ 2 / 4 ≤ 6145 / 1000 := by
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hM := tauM_le' hn
  have hS1 := tauS1_le hn hk
  have hS2 := uS_le hn hk
  have hU1 := tauU1_le hn
  have hU2 := uU_le hn
  set tM := tauM n (6 / 100) ((1 + deltaC n 12) * (4196 / 1000 / (n : ℝ))) with htM
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
  have hSM : tS + tM ≤ 34065 / 10000 / (n : ℝ) := by
    have : (2514 / 10000 / (n : ℝ)) + 31551 / 10000 / n = 34065 / 10000 / n := by ring
    linarith
  have hSM0 : 0 ≤ tS + tM := add_nonneg hS0 hM0
  have a2 : (tS + tM) ^ 2 ≤ (34065 / 10000 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hSM0 hSM 2
  have a3 : (tS + tM) * uu ≤ 34065 / 10000 / (n : ℝ) * (4319 / 10000 / n) :=
    mul_le_mul hSM hU2 hu0 (by positivity)
  have e : ((3165 / 1000 / (n : ℝ)) ^ 2 + (34065 / 10000 / (n : ℝ)) ^ 2 +
      2 * (34065 / 10000 / (n : ℝ) * (4319 / 10000 / n))) * (n : ℝ) ^ 2 / 4 =
      ((3165 / 1000) ^ 2 + (34065 / 10000) ^ 2 + 2 * (34065 / 10000 * (4319 / 10000))) / 4 := by
    field_simp
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by positivity
  have h5 : tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu ≤
      (3165 / 1000 / (n : ℝ)) ^ 2 + (34065 / 10000 / (n : ℝ)) ^ 2 +
        2 * (34065 / 10000 / (n : ℝ) * (4319 / 10000 / n)) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hn2
  have h7 : (((3165 / 1000 : ℝ)) ^ 2 + (34065 / 10000) ^ 2 +
      2 * (34065 / 10000 * (4319 / 10000))) / 4 ≤ 6145 / 1000 := by norm_num
  have e2 : (tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu) * (n : ℝ) ^ 2 / 4 =
      (tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu) * ((n : ℝ) ^ 2 / 4) := by ring
  have e3 : ((3165 / 1000 / (n : ℝ)) ^ 2 + (34065 / 10000 / (n : ℝ)) ^ 2 +
      2 * (34065 / 10000 / (n : ℝ) * (4319 / 10000 / n))) * ((n : ℝ) ^ 2 / 4) =
      ((3165 / 1000 / (n : ℝ)) ^ 2 + (34065 / 10000 / (n : ℝ)) ^ 2 +
      2 * (34065 / 10000 / (n : ℝ) * (4319 / 10000 / n))) * (n : ℝ) ^ 2 / 4 := by ring
  rw [e2]
  rw [e3, e] at h6
  linarith

/-- The sum of all charges is at most `1/100`, for `c_V ≤ 6.145`. -/
lemma total_le' {cV : ℝ} (hcV0 : 0 < cV) (hcV : cV ≤ 6145 / 1000) :
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
      have : (175 / 12 : ℝ) ^ 2 * cV ≤ (175 / 12) ^ 2 * (6145 / 1000) :=
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

/-! ## The conditional theorems at the level `99/100`, primitive hypotheses -/

/-- **The frame of Theorem 5 at the level `99/100` with the hypotheses in the primitive
quantities of the document (set II), for every `n ≥ 16 384`, `k ≥ 100n`, every atom count `J`.**
If there is a measurable set `X12` of values of `(W, (A₁, A₂))` with `Pr(X12ᶜ) ≤ 27/10000` on
which: the centre `b = bTW J` is not `0`; `τ̃₀ > 0`; `‖t_A·Cov_ξ(a₂)‖_op ≤ 1.192·γ_A/n`; the
centre error `t_A|ā₂ − b|² ≤ 0.470·γ_A/n`; and (V1) to (V4) of Lemma V hold with `ϑ = 0.3`,
`s_* = 0.18`, `M_P = 1.192`, `ξ_∥ = 0.0274`, `N22 = 18.334/n`, `N24 = 24.779/n` (`VOK`): then
the straight-line program `fullProg150 k n J` of Part 150 succeeds with probability at least
`99/100`. -/
theorem theorem5_cond_99_V (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ 27 / 10000)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ 1192 / 1000 * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bTW J (W, (A₁, A₂)) j) ≤
          470 / 1000 * (2 / (n : ℝ)) / n)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK (bTW J) W A₁ A₂ (3 / 10) (18 / 100) (1192 / 1000) (274 / 10000)
        (18334 / 1000 / (n : ℝ)) (24779 / 1000 / (n : ℝ))) :
    99 / 100 ≤ (jointP k n).real
      {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hMr0 : (0 : ℝ) < 1662 / 1000 * (2 / (n : ℝ)) / n := by positivity
  obtain ⟨hD, hw⟩ := DvV_num hn
  have he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ) := by
    rintro ⟨W, A₁, A₂⟩ hx'
    exact he_of_VOK hn1 (by norm_num) (hV W A₁ A₂ hx')
  have hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK (bTW J) W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n) := by
    intro W A₁ A₂ hx'
    have h := CrOK_of_cov (bh := bTW J) hn1 (hb _ hx')
      (Mcov := 1192 / 1000 * (2 / (n : ℝ)) / n) (Mb := 470 / 1000 * (2 / (n : ℝ)) / n)
      (by positivity) (hcov W A₁ A₂ hx') (hcen W A₁ A₂ hx')
    have e : 1192 / 1000 * (2 / (n : ℝ)) / n + 470 / 1000 * (2 / (n : ℝ)) / n =
        1662 / 1000 * (2 / (n : ℝ)) / n := by ring
    rw [e] at h
    exact h
  have hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ 4196 / 1000 / (n : ℝ) := fun W A₁ A₂ hx' =>
    (Dv_le_of_V (bTW J) W A₁ A₂ hn1 (hb _ hx') (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by positivity) (by positivity) hw (hV W A₁ A₂ hx')).trans hD
  have h := theorem5_frameProg (k := k) (n := n) (J := J) (by omega) (by omega) h12 hp12 hb he hτ
    hMr0 hCr hDv (δ := 6 / 100) (uF := 5) (Lc := 12) (by norm_num) (by norm_num) (by norm_num)
    (εW := 26 / 100) (θ := 38 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine le_trans ?_ h
  have hv := vbar_num' hn hk
  have hv0 := (vbar_pos' n k (δ := 6 / 100)
    (Dbar := (1 + deltaC n 12) * (4196 / 1000 / (n : ℝ))) (Ebar := 2 * (1 + deltaC n 12))
    (LF := LFc n 5) (Lc := 12) (by norm_num) hMr0).resolve_right hx0.ne'
  have ht := total_le' hn hv0 hv
  linarith

/-- The same for the estimator `gSampH bh k` with any measurable centre map `bh`. -/
theorem theorem5_cond_99_V_samp (hn : 16384 ≤ n) (hk : 100 * n ≤ k) {bh : CMap n}
    (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ 27 / 10000)
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ 1192 / 1000 * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j) ≤
          470 / 1000 * (2 / (n : ℝ)) / n)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK bh W A₁ A₂ (3 / 10) (18 / 100) (1192 / 1000) (274 / 10000)
        (18334 / 1000 / (n : ℝ)) (24779 / 1000 / (n : ℝ))) :
    99 / 100 ≤ (jointP k n).real
      {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hMr0 : (0 : ℝ) < 1662 / 1000 * (2 / (n : ℝ)) / n := by positivity
  obtain ⟨hD, hw⟩ := DvV_num hn
  have he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ) := by
    rintro ⟨W, A₁, A₂⟩ hx'
    exact he_of_VOK hn1 (by norm_num) (hV W A₁ A₂ hx')
  have hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK bh W A₁ A₂ (1662 / 1000 * (2 / (n : ℝ)) / n) := by
    intro W A₁ A₂ hx'
    have h := CrOK_of_cov (bh := bh) hn1 (hb _ hx')
      (Mcov := 1192 / 1000 * (2 / (n : ℝ)) / n) (Mb := 470 / 1000 * (2 / (n : ℝ)) / n)
      (by positivity) (hcov W A₁ A₂ hx') (hcen W A₁ A₂ hx')
    have e : 1192 / 1000 * (2 / (n : ℝ)) / n + 470 / 1000 * (2 / (n : ℝ)) / n =
        1662 / 1000 * (2 / (n : ℝ)) / n := by ring
    rw [e] at h
    exact h
  have hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv bh W A₁ A₂ ≤ 4196 / 1000 / (n : ℝ) := fun W A₁ A₂ hx' =>
    (Dv_le_of_V bh W A₁ A₂ hn1 (hb _ hx') (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by positivity) (by positivity) hw (hV W A₁ A₂ hx')).trans hD
  have h := theorem5_frameA12 (k := k) (n := n) (by omega) (by omega) hbh h12 hp12 hb he
    hMr0 hCr hDv (δ := 6 / 100) (uF := 5) (Lc := 12) (by norm_num) (by norm_num) (by norm_num)
    (εW := 26 / 100) (θ := 38 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine le_trans ?_ h
  have hv := vbar_num' hn hk
  have hv0 := (vbar_pos' n k (δ := 6 / 100)
    (Dbar := (1 + deltaC n 12) * (4196 / 1000 / (n : ℝ))) (Ebar := 2 * (1 + deltaC n 12))
    (LF := LFc n 5) (Lc := 12) (by norm_num) hMr0).resolve_right hx0.ne'
  have ht := total_le' hn hv0 hv
  linarith

end BstLean.Part151
