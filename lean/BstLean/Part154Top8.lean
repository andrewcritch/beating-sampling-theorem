import BstLean.Part154VOK8
import BstLean.Part154Meas8
import BstLean.Part154Top

/-!
# Part 154: a level for every `n ≥ 8192`, with no hypothesis
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part130 BstLean.Part150
open BstLean.Part29 (stdGauss)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part141 (cenA tauWA)
open BstLean.Part151 (VOK hU jointP)

section auxTop8

open BstLean.Part151
open scoped ENNReal NNReal
open BstLean.Part131
open BstLean.Part139 (gamK)
open BstLean.Part149 (thA tauOutOf)

variable {k n : ℕ}

private lemma sqrt_ge_Top8 (hn : 8192 ≤ n) : (905 / 10 : ℝ) ≤ √(n : ℝ) := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_sqrt' (by norm_num)]
  norm_num
  linarith

private lemma mF_ge_90_Top8 (hn : 8192 ≤ n) : 905 / 10 * (n : ℝ) ≤ mF n := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hs := sqrt_ge_Top8 hn
  have h := BstLean.Part139.mF_ge_s (n := n) (by omega)
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n) (sub_nonneg.mpr hs)]

private lemma mF_ge_big_Top8 (hn : 8192 ≤ n) : (741376 : ℝ) ≤ mF n := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have := mF_ge_90_Top8 hn
  linarith

private lemma two_PhiBar_three_Top8 {a : ℝ} (ha : 3 ≤ a) : 2 * PhiBar a ≤ 3 / 1000 := by
  have h1 := tail_anti ha
  have h2 := two_tail_three
  unfold PhiBar
  linarith

private lemma deltaC_le_Top8 (hn : 8192 ≤ n) : deltaC n 12 ≤ 796 / 10000 := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have h1 : (12 : ℝ) / n ≤ 12 / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h2 : √((12 : ℝ) / n) ≤ 383 / 10000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    refine h1.trans ?_
    norm_num
  have h3 : 2 * (12 : ℝ) / n ≤ 2 * 12 / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  unfold deltaC
  have h4 : (2 * 12 / 8192 : ℝ) ≤ 30 / 10000 := by norm_num
  linarith

/-- `t_F·L_F² ≤ 39.744/n` (`l_F ≤ 1.242` at `u_F = 5`). -/
private lemma tLF_le_Top8 (hn : 8192 ≤ n) :
    2 / (mF n : ℝ) * LFc n 5 ^ 2 ≤ 39744 / 1000 / (n : ℝ) ∧
      0 ≤ 2 / (mF n : ℝ) * LFc n 5 ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hm := mF_ge_90_Top8 hn
  have hmb := mF_ge_big_Top8 hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  have hm1 : 1 ≤ mF n := by
    have : (1 : ℝ) ≤ mF n := by linarith
    exact_mod_cast this
  set sm : ℝ := √(mF n : ℝ) with hsm
  have hsm2 : sm ^ 2 = mF n := Real.sq_sqrt hm0.le
  have hsm1 : (861 : ℝ) ≤ sm := by
    have h2 : (861 : ℝ) ^ 2 = 741321 := by norm_num
    rw [hsm]
    refine Real.le_sqrt_of_sq_le ?_
    rw [h2]; linarith
  have hsm0 : 0 < sm := by linarith
  have hsn : √(n : ℝ) ≤ 1052 / 10000 * sm := by
    rw [Real.sqrt_le_left (by positivity), mul_pow, hsm2]
    nlinarith
  have hsn0 : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg _
  have e := tF_LF_sq hn1 hm1 5
  have e' : 2 / (mF n : ℝ) * LFc n 5 ^ 2 =
      32 / (n : ℝ) * ((1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2) := by
    unfold LFc; exact e
  rw [e']
  have p1 : 1 + 5 / (2 * sm) ≤ 1 + 5 / 1722 := by
    have : 5 / (2 * sm) ≤ 5 / 1722 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have p10 : 0 ≤ 1 + 5 / (2 * sm) := by positivity
  have q1 : 1 + (√(n : ℝ) + 5) / sm ≤ 1 + 1052 / 10000 + 5 / 861 := by
    have h1 : (√(n : ℝ) + 5) / sm = √(n : ℝ) / sm + 5 / sm := by ring
    have h2 : √(n : ℝ) / sm ≤ 1052 / 10000 := by
      rw [div_le_iff₀ hsm0]; exact hsn
    have h3 : 5 / sm ≤ 5 / 861 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsm1
    rw [h1]; linarith
  have q10 : 0 ≤ 1 + (√(n : ℝ) + 5) / sm := by positivity
  have hl : (1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2 ≤ 1242 / 1000 := by
    calc (1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2
        ≤ (1 + 5 / 1722 : ℝ) ^ 2 * (1 + 1052 / 10000 + 5 / 861) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ p10 p1 2) (pow_le_pow_left₀ q10 q1 2) (by positivity)
            (by norm_num)
      _ ≤ 1242 / 1000 := by norm_num
  constructor
  · calc 32 / (n : ℝ) * ((1 + 5 / (2 * sm)) ^ 2 * (1 + (√(n : ℝ) + 5) / sm) ^ 2)
        ≤ 32 / (n : ℝ) * (1242 / 1000) := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = 39744 / 1000 / (n : ℝ) := by ring
  · positivity

private lemma chF_le_Top8 (hn : 8192 ≤ n) : chF n (6 / 100) ≤ 1214 / 10000000 := by
  have hmb := mF_ge_big_Top8 hn
  have hm0 : (0 : ℝ) < mF n := by linarith
  unfold chF
  have h1 : 432 / (mF n : ℝ) ^ 2 ≤ 432 / 741376 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hmb 2)
  have h2 : 1 + 63 / (mF n : ℝ) ≤ 1 + 63 / 741376 := by
    have : 63 / (mF n : ℝ) ≤ 63 / 741376 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hmb
    linarith
  calc 432 / (mF n : ℝ) ^ 2 * (1 + 63 / (mF n : ℝ)) * (1 / (6 / 100 : ℝ) ^ 4 + 1 / (6 / 100) ^ 4)
      ≤ 432 / 741376 ^ 2 * (1 + 63 / 741376) * (1 / (6 / 100 : ℝ) ^ 4 + 1 / (6 / 100) ^ 4) := by
        refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
        exact mul_le_mul h1 h2 (by positivity) (by norm_num)
    _ ≤ 1214 / 10000000 := by norm_num

section piecesA

variable (hn : 8192 ≤ n)
include hn

private lemma tauS1_le_Top8 (hk : 100 * n ≤ k) :
    √((1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * (2 * (1 + deltaC n 12))) / k) ≤
      2203 / 10000 / (n : ℝ) := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK : 100 * (n : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < k := by linarith
  have hd := deltaC_le_Top8 hn
  have hd0 := deltaC_nn n
  set dc := deltaC n 12
  rw [Real.sqrt_le_left (by positivity), div_pow, div_le_div_iff₀ hK0 (by positivity)]
  have e : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * (2 * (1 + dc))) * (n : ℝ) ^ 2 =
      (1 + 6 / 100) * (1 + 6 / 100) * 4 * (1 + dc) * n := by
    field_simp
    ring
  rw [e]
  have hA : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * 4 * (1 + dc) ≤ 100 * (2203 / 10000) ^ 2 := by
    nlinarith
  calc (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * 4 * (1 + dc) * n
      ≤ 100 * (2203 / 10000) ^ 2 * n := mul_le_mul_of_nonneg_right hA hx0.le
    _ = (2203 / 10000) ^ 2 * (100 * n) := by ring
    _ ≤ (2203 / 10000) ^ 2 * k := mul_le_mul_of_nonneg_left hK (by norm_num)

private lemma uS_le_Top8 (hk : 100 * n ≤ k) : uS n k (LFc n 5) 12 ≤ 483 / 10000 / (n : ℝ) := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hK : 100 * (n : ℝ) ≤ k := by exact_mod_cast hk
  have hK0 : (0 : ℝ) < k := by linarith
  obtain ⟨hT, hT0⟩ := tLF_le_Top8 hn
  set T := 2 / (mF n : ℝ) * LFc n 5 ^ 2
  unfold uS ellS
  rw [← Real.sqrt_mul (by norm_num), Real.sqrt_le_left (by positivity)]
  have h1 : T * (2 / (n : ℝ)) / k ≤ 39744 / 1000 / (n : ℝ) * (2 / (n : ℝ)) / (100 * n) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hT (by positivity))
      (by positivity) hK
  have h2 : (2 * 12 : ℝ) * (39744 / 1000 / (n : ℝ) * (2 / (n : ℝ)) / (100 * n)) ≤
      (483 / 10000 / (n : ℝ)) ^ 2 := by
    rw [div_pow]
    have e : (2 * 12 : ℝ) * (39744 / 1000 / (n : ℝ) * (2 / (n : ℝ)) / (100 * n)) =
        (2 * 12 * (39744 / 1000) * 2 / 100) / (n : ℝ) ^ 3 := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * 12 * (39744 / 1000) * 2 / 100 : ℝ) ≤ (483 / 10000) ^ 2 * 8192 := by norm_num
    have h3 : (2 * 12 * (39744 / 1000) * 2 / 100 : ℝ) ≤ (483 / 10000) ^ 2 * n := by nlinarith
    calc (2 * 12 * (39744 / 1000) * 2 / 100 : ℝ) * (n : ℝ) ^ 2
        ≤ (483 / 10000) ^ 2 * n * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (483 / 10000) ^ 2 * (n : ℝ) ^ 3 := by ring
  have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2 * 12)
  linarith

end piecesA

/-- The bracket of Lemma V in the variable `s = √n ≥ (905 / 10)`: at most `2.098`; and `ϖ < 1`. -/
private lemma DvV_core_Top8 {s : ℝ} (hs : 905 / 10 ≤ s) (hs2 : (8192 : ℝ) ≤ s ^ 2) :
    (√(kappaV (3 / 10) (24779 / 1000 / s ^ 2) * (12578 / 10000)) +
        s * rthV (3 / 10) (18340 / 1000 / s ^ 2) (24779 / 1000 / s ^ 2)) ^ 2 + 575 / 10000 +
      s ^ 2 * dfrakV (s ^ 2) (179 / 1000) (12578 / 10000) (575 / 10000) (18340 / 1000 / s ^ 2) ≤
        2989 / 1000 ∧
    eDeltaV (s ^ 2) (179 / 1000) (12578 / 10000) (575 / 10000) (18340 / 1000 / s ^ 2) / (179 / 1000) <
      1 := by
  have hs0 : 0 < s := by linarith
  have hs3 : (905 / 10 : ℝ) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ (by norm_num) hs 3
  set N22 : ℝ := 18340 / 1000 / s ^ 2 with h22
  set N24 : ℝ := 24779 / 1000 / s ^ 2 with h24
  have a22 : N22 ≤ 18340 / 1000 / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
  have a24 : N24 ≤ 24779 / 1000 / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
  have p22 : 0 ≤ N22 := by rw [h22]; positivity
  have p24 : 0 ≤ N24 := by rw [h24]; positivity
  -- `κ_ϑ`
  have hk : kappaV (3 / 10) N24 ≤ 101004 / 100000 := by
    unfold kappaV
    have e : (1 + N24 / (1 - 3 / 10)) ^ 2 +
        661 / 100 * N24 ^ 2 / ((1 - 3 / 10) ^ 2 * (3 / 10) ^ 2) =
        1 + 20 / 7 * N24 + (100 / 49 + 661 / 100 / ((7 / 10) ^ 2 * (3 / 10) ^ 2)) * N24 ^ 2 := by
      ring
    rw [e]
    have h2 : N24 ^ 2 ≤ (24779 / 1000 / 8192) ^ 2 := pow_le_pow_left₀ p24 a24 2
    have c1 := mul_le_mul_of_nonneg_left h2
      (by norm_num : (0 : ℝ) ≤ 100 / 49 + 661 / 100 / ((7 / 10) ^ 2 * (3 / 10) ^ 2))
    have c2 : (1 : ℝ) + 20 / 7 * (24779 / 1000 / 8192) +
        (100 / 49 + 661 / 100 / ((7 / 10) ^ 2 * (3 / 10) ^ 2)) * (24779 / 1000 / 8192) ^ 2 ≤
        101004 / 100000 := by norm_num
    linarith
  have hk0 : 0 ≤ kappaV (3 / 10) N24 := by unfold kappaV; positivity
  have hsq : √(kappaV (3 / 10) N24 * (12578 / 10000)) ≤ 112714 / 100000 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have c : (101004 / 100000 : ℝ) * (12578 / 10000) ≤ (112714 / 100000) ^ 2 := by norm_num
    nlinarith
  -- `√n·𝔯_ϑ`
  have e1 : s * N22 = 18340 / 1000 / s := by
    rw [h22]; field_simp
  have t1 : s * N22 ≤ 18340 / 1000 / (905 / 10) := by
    rw [e1]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have t10 : 0 ≤ s * N22 := by positivity
  have hr : s * rthV (3 / 10) N22 N24 ≤ 22107 / 100000 := by
    unfold rthV
    have e2 : s * (2 * N24 ^ 2 / (3 / 10) ^ 2) = 2 * (24779 / 1000) ^ 2 / (3 / 10) ^ 2 / s ^ 3 := by
      rw [h24]; field_simp
    have t2 : 2 * (24779 / 1000 : ℝ) ^ 2 / (3 / 10) ^ 2 / s ^ 3 ≤
        2 * (24779 / 1000) ^ 2 / (3 / 10) ^ 2 / (905 / 10) ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs3
    have c : (18340 / 1000 / (905 / 10) : ℝ) + 2 * (24779 / 1000) ^ 2 / (3 / 10) ^ 2 / (905 / 10) ^ 3 ≤
        22107 / 100000 := by norm_num
    have e3 : s * (N22 + 2 * N24 ^ 2 / (3 / 10) ^ 2) =
        s * N22 + s * (2 * N24 ^ 2 / (3 / 10) ^ 2) := by ring
    rw [e3, e2]
    linarith
  have hr0 : 0 ≤ s * rthV (3 / 10) N22 N24 := by unfold rthV; positivity
  have hA : (√(kappaV (3 / 10) N24 * (12578 / 10000)) + s * rthV (3 / 10) N22 N24) ^ 2 ≤
      181768 / 100000 := by
    have h0 : 0 ≤ √(kappaV (3 / 10) N24 * (12578 / 10000)) + s * rthV (3 / 10) N22 N24 :=
      add_nonneg (Real.sqrt_nonneg _) hr0
    have h1 : √(kappaV (3 / 10) N24 * (12578 / 10000)) + s * rthV (3 / 10) N22 N24 ≤
        112714 / 100000 + 22107 / 100000 := by linarith
    calc _ ≤ (112714 / 100000 + 22107 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ ≤ 181768 / 100000 := by norm_num
  -- `e_Δ`
  set eD : ℝ := eDeltaV (s ^ 2) (179 / 1000) (12578 / 10000) (575 / 10000) N22 with heD
  have heD' : eD = N22 * (2 + N22) + (2 * (12578 / 10000) + 575 / 10000) / s ^ 2 +
      2 * √((1 - 179 / 1000) * (575 / 10000) / s ^ 2) := rfl
  have hroot : √((1 - 179 / 1000) * (575 / 10000) / s ^ 2) ≤ 217273 / 1000000 / s := by
    rw [Real.sqrt_le_left (by positivity), div_pow]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hroot0 : 0 ≤ √((1 - 179 / 1000) * (575 / 10000) / s ^ 2) := Real.sqrt_nonneg _
  have heD0 : 0 ≤ eD := by rw [heD']; positivity
  have hq : s * eD ≤ 86874 / 100000 := by
    have t2 : s * N22 * (2 + N22) ≤ 18340 / 1000 / (905 / 10) * (2 + 18340 / 1000 / 8192) :=
      mul_le_mul t1 (by linarith) (by linarith) (by norm_num)
    have e3 : s * ((2 * (12578 / 10000) + 575 / 10000) / s ^ 2) =
        (2 * (12578 / 10000) + 575 / 10000) / s := by field_simp
    have t3 : (2 * (12578 / 10000) + 575 / 10000 : ℝ) / s ≤
        (2 * (12578 / 10000) + 575 / 10000) / (905 / 10) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have t4 : s * √((1 - 179 / 1000) * (575 / 10000) / s ^ 2) ≤ 217273 / 1000000 := by
      calc s * √((1 - 179 / 1000) * (575 / 10000) / s ^ 2) ≤ s * (217273 / 1000000 / s) :=
            mul_le_mul_of_nonneg_left hroot hs0.le
        _ = 217273 / 1000000 := by field_simp
    have e4 : s * eD = s * N22 * (2 + N22) + s * ((2 * (12578 / 10000) + 575 / 10000) / s ^ 2) +
        2 * (s * √((1 - 179 / 1000) * (575 / 10000) / s ^ 2)) := by rw [heD']; ring
    have c : (18340 / 1000 / (905 / 10) : ℝ) * (2 + 18340 / 1000 / 8192) +
        (2 * (12578 / 10000) + 575 / 10000) / (905 / 10) + 2 * (217273 / 1000000) ≤ 86874 / 100000 := by
      norm_num
    rw [e4, e3]
    linarith
  have hq0 : 0 ≤ s * eD := by positivity
  have he0 : eD ≤ 95994 / 10000000 := by
    have h1 : eD ≤ 86874 / 100000 / s := by
      rw [le_div_iff₀ hs0]; linarith
    have h2 : (86874 / 100000 : ℝ) / s ≤ 86874 / 100000 / (905 / 10) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    have h3 : (86874 / 100000 : ℝ) / (905 / 10) ≤ 95994 / 10000000 := by norm_num
    linarith
  -- `n·𝔡`
  have hd : dfrakV (s ^ 2) (179 / 1000) (12578 / 10000) (575 / 10000) N22 =
      eD ^ 2 / (179 / 1000 * (2 - eD / (179 / 1000)) ^ 2) := rfl
  have hD : s ^ 2 * dfrakV (s ^ 2) (179 / 1000) (12578 / 10000) (575 / 10000) N22 ≤
      111295 / 100000 := by
    rw [hd]
    have hb1 : 2 - (95994 / 10000000 : ℝ) / (179 / 1000) ≤ 2 - eD / (179 / 1000) := by
      have : eD / (179 / 1000) ≤ (95994 / 10000000 : ℝ) / (179 / 1000) :=
        div_le_div_of_nonneg_right he0 (by norm_num)
      linarith
    have hden : (179 / 1000 : ℝ) * (2 - 95994 / 10000000 / (179 / 1000)) ^ 2 ≤
        179 / 1000 * (2 - eD / (179 / 1000)) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hb1 2) (by norm_num)
    have hden0 : (0 : ℝ) < 179 / 1000 * (2 - 95994 / 10000000 / (179 / 1000)) ^ 2 := by norm_num
    have e : s ^ 2 * (eD ^ 2 / (179 / 1000 * (2 - eD / (179 / 1000)) ^ 2)) =
        (s * eD) ^ 2 / (179 / 1000 * (2 - eD / (179 / 1000)) ^ 2) := by ring
    rw [e]
    have hnum : (s * eD) ^ 2 ≤ (86874 / 100000) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    calc (s * eD) ^ 2 / (179 / 1000 * (2 - eD / (179 / 1000)) ^ 2)
        ≤ (86874 / 100000) ^ 2 / (179 / 1000 * (2 - 95994 / 10000000 / (179 / 1000)) ^ 2) :=
          div_le_div₀ (by norm_num) hnum hden0 hden
      _ ≤ 111295 / 100000 := by norm_num
  constructor
  · have c : (181768 / 100000 : ℝ) + 575 / 10000 + 111295 / 100000 ≤ 2989 / 1000 := by norm_num
    linarith
  · rw [div_lt_one (by norm_num)]
    linarith

/-- **Lemma V at the constants of the document** (`ϑ = 0.3`, `s_* = 0.18`, `M_P = 1.192`,
`ξ_∥ = 0.0274`, `n·N22 = 18.334`, `n·N24 = 24.779`): `DvV ≤ 4.196/n` for every `n ≥ 16 384`,
and the condition `ϖ < 1`. -/
private theorem DvV_num_Top8 (hn : 8192 ≤ n) :
    DvV n (3 / 10) (179 / 1000) (12578 / 10000) (575 / 10000) (18340 / 1000 / (n : ℝ))
        (24779 / 1000 / (n : ℝ)) ≤ 5978 / 1000 / (n : ℝ) ∧
    eDeltaV n (179 / 1000) (12578 / 10000) (575 / 10000) (18340 / 1000 / (n : ℝ)) / (179 / 1000) <
      1 := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hsq : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt hx0.le).symm
  have hs : (905 / 10 : ℝ) ≤ √(n : ℝ) := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num; linarith
  unfold DvV
  generalize √(n : ℝ) = s at hsq hs ⊢
  have hs2 : (8192 : ℝ) ≤ s ^ 2 := by rw [← hsq]; exact hx
  rw [hsq]
  obtain ⟨h1, h2⟩ := DvV_core_Top8 hs hs2
  have hs0 : 0 < s := by linarith
  refine ⟨?_, h2⟩
  calc 2 / s ^ 2 * ((√(kappaV (3 / 10) (24779 / 1000 / s ^ 2) * (12578 / 10000)) +
          s * rthV (3 / 10) (18340 / 1000 / s ^ 2) (24779 / 1000 / s ^ 2)) ^ 2 + 575 / 10000 +
        s ^ 2 * dfrakV (s ^ 2) (179 / 1000) (12578 / 10000) (575 / 10000) (18340 / 1000 / s ^ 2))
      ≤ 2 / s ^ 2 * (2989 / 1000) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 5978 / 1000 / s ^ 2 := by ring

section pieces

variable (hn : 8192 ≤ n)
include hn

private lemma tauM_le_Top8 :
    tauM n (6 / 100) ((1 + deltaC n 12) * (5978 / 1000 / (n : ℝ))) ≤ 38083 / 10000 / (n : ℝ) := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hd := deltaC_le_Top8 hn
  have hd0 := deltaC_nn n
  set dc := deltaC n 12
  unfold tauM
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have e : (1 + 6 / 100 : ℝ) * (1 + 6 / 100) * (2 / (n : ℝ) * ((1 + dc) * (5978 / 1000 / n))) *
      (n : ℝ) ^ 2 = (1 + 6 / 100) * (1 + 6 / 100) * 2 * (5978 / 1000) * (1 + dc) := by
    field_simp
  rw [e]
  nlinarith

private lemma uU_le_Top8 : uU n (LFc n 5) (18378 / 10000 * (2 / (n : ℝ)) / n) 12 ≤ 6543 / 10000 / (n : ℝ) := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hT, hT0⟩ := tLF_le_Top8 hn
  set T := 2 / (mF n : ℝ) * LFc n 5 ^ 2
  unfold uU ellU
  rw [← Real.sqrt_mul (by norm_num), Real.sqrt_le_left (by positivity)]
  have h1 : T * (18378 / 10000 * (2 / (n : ℝ)) / n) ≤
      39744 / 1000 / (n : ℝ) * (18378 / 10000 * (2 / (n : ℝ)) / n) :=
    mul_le_mul_of_nonneg_right hT (by positivity)
  have h2 : (2 * 12 : ℝ) * (39744 / 1000 / (n : ℝ) * (18378 / 10000 * (2 / (n : ℝ)) / n)) ≤
      (6543 / 10000 / (n : ℝ)) ^ 2 := by
    rw [div_pow]
    have e : (2 * 12 : ℝ) * (39744 / 1000 / (n : ℝ) * (18378 / 10000 * (2 / (n : ℝ)) / n)) =
        (2 * 12 * (39744 / 1000) * (18378 / 10000) * 2) / (n : ℝ) ^ 3 := by
      field_simp
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (2 * 12 * (39744 / 1000) * (18378 / 10000) * 2 : ℝ) ≤ (6543 / 10000) ^ 2 * 8192 := by
      norm_num
    have h3 : (2 * 12 * (39744 / 1000) * (18378 / 10000) * 2 : ℝ) ≤ (6543 / 10000) ^ 2 * n := by
      nlinarith
    calc (2 * 12 * (39744 / 1000) * (18378 / 10000) * 2 : ℝ) * (n : ℝ) ^ 2
        ≤ (6543 / 10000) ^ 2 * n * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (6543 / 10000) ^ 2 * (n : ℝ) ^ 3 := by ring
  have h4 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2 * 12)
  linarith

private lemma tauU1_le_Top8 :
    √(18378 / 10000 * (2 / (n : ℝ)) / n * (2 * (1 + 6 / 100) * (1 + 6 / 100))) ≤
      28740 / 10000 / (n : ℝ) := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  rw [Real.sqrt_le_left (by positivity), div_pow, le_div_iff₀ (by positivity)]
  have e : (18378 / 10000 * (2 / (n : ℝ)) / n * (2 * (1 + 6 / 100) * (1 + 6 / 100))) * (n : ℝ) ^ 2 =
      18378 / 10000 * 2 * (2 * (1 + 6 / 100) * (1 + 6 / 100)) := by
    field_simp
  rw [e]
  norm_num

/-- **The variance coefficient**: `c_V = vbar·n²/4 ≤ 6.145` for every `n ≥ 16 384`,
`k ≥ 100n`, at `δ = 6/100`, `L_c = 12`, `u_F = 5`, `M_r = 1.662·(2/n)/n`, `D̄_v = 4.196/n`. -/
private theorem vbar_num_Top8 (hk : 100 * n ≤ k) :
    vbar n k (6 / 100) ((1 + deltaC n 12) * (5978 / 1000 / (n : ℝ))) (2 * (1 + deltaC n 12))
      (LFc n 5) (18378 / 10000 * (2 / (n : ℝ)) / n) 12 * (n : ℝ) ^ 2 / 4 ≤ 8602 / 1000 := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hM := tauM_le_Top8 hn
  have hS1 := tauS1_le_Top8 hn hk
  have hS2 := uS_le_Top8 hn hk
  have hU1 := tauU1_le_Top8 hn
  have hU2 := uU_le_Top8 hn
  set tM := tauM n (6 / 100) ((1 + deltaC n 12) * (5978 / 1000 / (n : ℝ))) with htM
  set uu := uU n (LFc n 5) (18378 / 10000 * (2 / (n : ℝ)) / n) 12 with huu
  set us := uS n k (LFc n 5) 12 with hus
  have hM0 : 0 ≤ tM := by rw [htM]; unfold tauM; exact Real.sqrt_nonneg _
  have hu0 : 0 ≤ uu := uU_nonneg _ _ _ _
  have hs0 : 0 ≤ us := uS_nonneg _ _ _ _
  have hS : tauS n k (6 / 100) (2 * (1 + deltaC n 12)) (LFc n 5) 12 ≤ 2686 / 10000 / (n : ℝ) := by
    unfold tauS
    have : (2203 / 10000 / (n : ℝ)) + 483 / 10000 / n = 2686 / 10000 / n := by ring
    linarith
  have hS0 : 0 ≤ tauS n k (6 / 100) (2 * (1 + deltaC n 12)) (LFc n 5) 12 := by
    unfold tauS
    exact add_nonneg (Real.sqrt_nonneg _) hs0
  have hU : tauU n (6 / 100) (LFc n 5) (18378 / 10000 * (2 / (n : ℝ)) / n) 12 ≤
      35283 / 10000 / (n : ℝ) := by
    unfold tauU
    have : (28740 / 10000 / (n : ℝ)) + 6543 / 10000 / n = 35283 / 10000 / n := by ring
    linarith
  have hU0 : 0 ≤ tauU n (6 / 100) (LFc n 5) (18378 / 10000 * (2 / (n : ℝ)) / n) 12 := by
    unfold tauU
    exact add_nonneg (Real.sqrt_nonneg _) hu0
  unfold vbar
  set tS := tauS n k (6 / 100) (2 * (1 + deltaC n 12)) (LFc n 5) 12
  set tU := tauU n (6 / 100) (LFc n 5) (18378 / 10000 * (2 / (n : ℝ)) / n) 12
  have a1 : tU ^ 2 ≤ (35283 / 10000 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hU0 hU 2
  have hSM : tS + tM ≤ 40769 / 10000 / (n : ℝ) := by
    have : (2686 / 10000 / (n : ℝ)) + 38083 / 10000 / n = 40769 / 10000 / n := by ring
    linarith
  have hSM0 : 0 ≤ tS + tM := add_nonneg hS0 hM0
  have a2 : (tS + tM) ^ 2 ≤ (40769 / 10000 / (n : ℝ)) ^ 2 := pow_le_pow_left₀ hSM0 hSM 2
  have a3 : (tS + tM) * uu ≤ 40769 / 10000 / (n : ℝ) * (6543 / 10000 / n) :=
    mul_le_mul hSM hU2 hu0 (by positivity)
  have e : ((35283 / 10000 / (n : ℝ)) ^ 2 + (40769 / 10000 / (n : ℝ)) ^ 2 +
      2 * (40769 / 10000 / (n : ℝ) * (6543 / 10000 / n))) * (n : ℝ) ^ 2 / 4 =
      ((35283 / 10000) ^ 2 + (40769 / 10000) ^ 2 + 2 * (40769 / 10000 * (6543 / 10000))) / 4 := by
    field_simp
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by positivity
  have h5 : tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu ≤
      (35283 / 10000 / (n : ℝ)) ^ 2 + (40769 / 10000 / (n : ℝ)) ^ 2 +
        2 * (40769 / 10000 / (n : ℝ) * (6543 / 10000 / n)) := by linarith
  have h6 := mul_le_mul_of_nonneg_right h5 hn2
  have h7 : (((35283 / 10000 : ℝ)) ^ 2 + (40769 / 10000) ^ 2 +
      2 * (40769 / 10000 * (6543 / 10000))) / 4 ≤ 8602 / 1000 := by norm_num
  have e2 : (tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu) * (n : ℝ) ^ 2 / 4 =
      (tU ^ 2 + (tS + tM) ^ 2 + 2 * (tS + tM) * uu) * ((n : ℝ) ^ 2 / 4) := by ring
  have e3 : ((35283 / 10000 / (n : ℝ)) ^ 2 + (40769 / 10000 / (n : ℝ)) ^ 2 +
      2 * (40769 / 10000 / (n : ℝ) * (6543 / 10000 / n))) * ((n : ℝ) ^ 2 / 4) =
      ((35283 / 10000 / (n : ℝ)) ^ 2 + (40769 / 10000 / (n : ℝ)) ^ 2 +
      2 * (40769 / 10000 / (n : ℝ) * (6543 / 10000 / n))) * (n : ℝ) ^ 2 / 4 := by ring
  rw [e2]
  rw [e3, e] at h6
  linarith

end pieces

/-- The sum of all charges except `Pr(X12ᶜ)` is at most `15650/10⁶` (`n ≥ 8192`, `κ = 1/3`,
`ε_W = 17/100`, `θ = 39/100`, `c_V ≤ 8.602`). -/
private lemma total_le_Top8 (hn : 8192 ≤ n) {cV : ℝ} (hcV0 : 0 < cV) (hcV : cV ≤ 8602 / 1000)
    (p : ℝ) :
    1 / (n : ℝ) + 1 / 3 *
          (4849 / 20000 / ((17 / 100 : ℝ) ^ 2 * (39 / 100 * (222757 / 1000000))) / n) +
        (p + Real.exp (-12) + 2 * Real.exp (-(5 : ℝ) ^ 2 / 2) + 3 * chF n (6 / 100) +
          3 * Real.exp (-12)) +
        2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 39 / 100) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - 17 / 100) * √(n * (39 / 100 * (222757 / 1000000)) / cV)) ≤
      p + 15650 / 1000000 := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have t1 : 1 / (n : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hx
  have t2 : 4849 / 20000 / ((17 / 100 : ℝ) ^ 2 * (39 / 100 * (222757 / 1000000))) / n ≤
      4849 / 20000 / ((17 / 100 : ℝ) ^ 2 * (39 / 100 * (222757 / 1000000))) / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t3 : 2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 39 / 100) * (222757 / 1000000)) ^ 2 / n ≤
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 39 / 100) * (222757 / 1000000)) ^ 2 / 8192 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have t4 := exp_neg_twelve
  have t5 : Real.exp (-(5 : ℝ) ^ 2 / 2) ≤ Real.exp (-12) :=
    Real.exp_le_exp.mpr (by norm_num)
  have t6 := chF_le_Top8 hn
  have t7 : 2 * PhiBar ((1 / 2 - 17 / 100) *
      √(n * (39 / 100 * (222757 / 1000000)) / cV)) ≤ 3 / 1000 := by
    refine two_PhiBar_three_Top8 ?_
    have h1 : (100 / 11 : ℝ) ≤ √(n * (39 / 100 * (222757 / 1000000)) / cV) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [le_div_iff₀ hcV0]
      have : (100 / 11 : ℝ) ^ 2 * cV ≤ (100 / 11) ^ 2 * (8602 / 1000) :=
        mul_le_mul_of_nonneg_left hcV (by norm_num)
      nlinarith
    nlinarith
  have t8 : (1 : ℝ) / 8192 + 1 / 3 *
        (4849 / 20000 / ((17 / 100 : ℝ) ^ 2 * (39 / 100 * (222757 / 1000000))) / 8192) +
      (62 / 10000000 + 2 * (62 / 10000000) + 3 * (1214 / 10000000) + 3 * (62 / 10000000)) +
      2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 39 / 100) * (222757 / 1000000)) ^ 2 / 8192 +
      3 / 1000 ≤ 15650 / 1000000 := by norm_num
  linarith

/-- The hypotheses of the frame from the primitive hypotheses, for any centre map `bh`. -/
private lemma AstageV_Top8 (hn : 8192 ≤ n) {bh : CMap n}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hb : ∀ x ∈ X12, bh x ≠ 0)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ 12578 / 10000 * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bh (W, (A₁, A₂)) j) ≤
          580 / 1000 * (2 / (n : ℝ)) / n)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK bh W A₁ A₂ (3 / 10) (179 / 1000) (12578 / 10000) (575 / 10000)
        (18340 / 1000 / (n : ℝ)) (24779 / 1000 / (n : ℝ))) :
    (∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bh x) ≤ 2 / (n : ℝ)) ∧
    (∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      CrOK bh W A₁ A₂ (18378 / 10000 * (2 / (n : ℝ)) / n)) ∧
    (∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv bh W A₁ A₂ ≤ 5978 / 1000 / (n : ℝ)) := by
  have hn1 : 1 ≤ n := by omega
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  obtain ⟨hD, hw⟩ := DvV_num_Top8 hn
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨W, A₁, A₂⟩ hx'
    exact he_of_VOK hn1 (by norm_num) (hV W A₁ A₂ hx')
  · intro W A₁ A₂ hx'
    have h := CrOK_of_cov (bh := bh) hn1 (hb _ hx')
      (Mcov := 12578 / 10000 * (2 / (n : ℝ)) / n) (Mb := 580 / 1000 * (2 / (n : ℝ)) / n)
      (by positivity) (hcov W A₁ A₂ hx') (hcen W A₁ A₂ hx')
    have e : 12578 / 10000 * (2 / (n : ℝ)) / n + 580 / 1000 * (2 / (n : ℝ)) / n =
        18378 / 10000 * (2 / (n : ℝ)) / n := by ring
    rw [e] at h
    exact h
  · exact fun W A₁ A₂ hx' =>
      (Dv_le_of_V bh W A₁ A₂ hn1 (hb _ hx') (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by positivity) (by positivity) hw (hV W A₁ A₂ hx')).trans hD

/-- The common step: the bound of `theorem5_frameProgG` at the parameters of this file, for a
charge `p12` of the `A`-stage event, under the primitive hypotheses. -/
private lemma frameGV_at_Top8 (hn : 8192 ≤ n) (hk : 100 * n ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1)
    (hcov : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      ∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ 12578 / 10000 * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2)
    (hcen : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bTW J (W, (A₁, A₂)) j) ≤
          580 / 1000 * (2 / (n : ℝ)) / n)
    (hV : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      VOK (bTW J) W A₁ A₂ (3 / 10) (179 / 1000) (12578 / 10000) (575 / 10000)
        (18340 / 1000 / (n : ℝ)) (24779 / 1000 / (n : ℝ))) :
    ∃ cV : ℝ, 0 < cV ∧ cV ≤ 8602 / 1000 ∧
    1 - (1 / (n : ℝ) + 1 / 3 *
          (4849 / 20000 / ((17 / 100 : ℝ) ^ 2 * (39 / 100 * (222757 / 1000000))) / n) +
        (p12 + Real.exp (-12) + 2 * Real.exp (-(5 : ℝ) ^ 2 / 2) + 3 * chF n (6 / 100) +
          3 * Real.exp (-12)) +
        2 * (78728 / 100000 : ℝ) ^ 2 / ((1 - 39 / 100) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - 17 / 100) * √(n * (39 / 100 * (222757 / 1000000)) / cV))) ≤
      (jointP k n).real
        {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
          Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hMr0 : (0 : ℝ) < 18378 / 10000 * (2 / (n : ℝ)) / n := by positivity
  obtain ⟨he, hCr, hDv⟩ := AstageV_Top8 hn hb hcov hcen hV
  have h := theorem5_frameProgG (κ := 1 / 3) (fun a ha => two_PhiBar_le_third ha)
    (k := k) (n := n) (J := J) (by omega) (by omega) h12 hp12 hb he hτ
    hMr0 hCr hDv (δ := 6 / 100) (uF := 5) (Lc := 12) (by norm_num) (by norm_num) (by norm_num)
    (εW := 17 / 100) (θ := 39 / 100) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hv := vbar_num_Top8 hn hk
  have hv0 := (vbar_pos' n k (δ := 6 / 100)
    (Dbar := (1 + deltaC n 12) * (5978 / 1000 / (n : ℝ))) (Ebar := 2 * (1 + deltaC n 12))
    (LF := LFc n 5) (Lc := 12) (by norm_num) hMr0).resolve_right hx0.ne'
  exact ⟨_, hv0, hv, h⟩

end auxTop8

private lemma exp_neg_eight_Top8 : rexp (-8) ≤ 336 / 1000000 := by
  have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hp : (2.718 : ℝ) ^ 8 ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) he.le 8
  have hE : (2978 : ℝ) ≤ Real.exp 8 := by
    rw [h8]
    refine le_trans ?_ hp
    norm_num
  rw [Real.exp_neg, inv_eq_one_div]
  refine (one_div_le_one_div_of_le (by norm_num) hE).trans ?_
  norm_num

private lemma charge_Top8 {n : ℕ} (hn : 8192 ≤ n) :
    1 / (n : ℝ) + (1 / (n : ℝ) + 2 * rexp (-8)) +
      (rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000) ≤ 1105 / 1000000 := by
  have hx : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have t1 : 1 / (n : ℝ) ≤ 1 / 8192 := one_div_le_one_div_of_le (by norm_num) hx
  have t2 := exp_neg_eight_Top8
  have t3 := BstLean.Part151.exp_neg_twelve
  have t4 : rexp (-(n : ℝ) / 2) ≤ rexp (-12) := Real.exp_le_exp.mpr (by linarith)
  have t5 : 3445 / (n : ℝ) ^ 2 ≤ 3445 / (8192 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_left₀ (by norm_num) hx 2)
  have t6 : (1 : ℝ) / 8192 + (1 / 8192 + 2 * (336 / 1000000)) +
      (62 / 10000000 + 13 * (62 / 10000000) + 3445 / (8192 : ℝ) ^ 2 + 5 / 100000) ≤
      1105 / 1000000 := by norm_num
  linarith

private lemma hidGauss_eq_Top8 (n : ℕ) :
    hidGauss n (mA n) = BstLean.Part153.nuA n := rfl

private lemma hfam_Top8 {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (hidGauss n (mA n)).real {θ | ((c, τ), θ) ∉ SC8 n} ≤
      rexp (-(n : ℝ) / 2) + 13 * rexp (-12) + 3445 / (n : ℝ) ^ 2 + 5 / 100000 := by
  have h := GoodC_prob hn n c hτ
  have e : {θ : HidParam n (mA n) | ((c, τ), θ) ∉ SC8 n} = (GoodC n n c τ)ᶜ := by
    ext θ
    rfl
  rw [e, hidGauss_eq_Top8]
  exact h

private lemma hA_Top8 {n : ℕ} (hn : 8192 ≤ n)
    (hpos : ∀ x ∈ BstLean.Part151.X12famW n (Wd8 n) (SC8 n), 0 < tauWA x.1)
    (hwd : ∀ x ∈ BstLean.Part151.X12famW n (Wd8 n) (SC8 n), (cenA x.1, tauWA x.1) ∈ Wd8 n)
    (W : MlpParam (2 * n) (mW n) n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (hx : (W, ((A₁, A₂) : HidParam n (mA n))) ∈ BstLean.Part151.X12famW n (Wd8 n) (SC8 n)) :
    bTW n (W, ((A₁, A₂) : HidParam n (mA n))) ≠ 0 ∧
    (∀ w : Fin (mA n) → ℝ, 2 / (mA n : ℝ) * ∫ ξ,
        (∑ j, (hU W A₁ A₂ ξ j - ∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) * w j) ^ 2
          ∂stdGauss (Fin n) ≤ 12578 / 10000 * (2 / (n : ℝ)) / n * ∑ j, w j ^ 2) ∧
    2 / (mA n : ℝ) * normSq (fun j =>
        (∫ ζ, hU W A₁ A₂ ζ j ∂stdGauss (Fin n)) - bTW n (W, (A₁, A₂)) j) ≤
          580 / 1000 * (2 / (n : ℝ)) / n ∧
    VOK (bTW n) W A₁ A₂ (3 / 10) (179 / 1000) (12578 / 10000) (575 / 10000)
      (18340 / 1000 / (n : ℝ)) (24779 / 1000 / (n : ℝ)) := by
  have hp : 0 < tauWA W := hpos (W, ((A₁, A₂) : HidParam n (mA n))) hx
  have hw : (cenA W, tauWA W) ∈ Wd8 n := hwd (W, ((A₁, A₂) : HidParam n (mA n))) hx
  have h0 := hx
  unfold BstLean.Part151.X12famW BstLean.Part151.X12fam at h0
  obtain ⟨⟨_, h1⟩, _⟩ := h0
  have h2 : (A₁, A₂) ∈ GoodC n n (cenA W) (tauWA W) := by
    unfold SC8 at h1
    exact h1
  exact A12_of_GoodC8 hn W hp hw h2

/-- **The level that the charges give for `n ≥ 8192`** (total at most `17/1000`): the arithmetic
program of Part 150 (`J = n` atoms, `k ≥ 100n`) succeeds with probability at least `983/1000`. -/
theorem theorem5_154_8192' {n k : ℕ} (hn : 8192 ≤ n) (hk : 100 * n ≤ k) :
    983 / 1000 ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨hm, hp, hpos, hwd⟩ := BstLean.Part151.X12_of_family_window (by omega)
    (measurableSet_Wd8 n) (measurableSet_SC8 hn1) (by positivity)
    (fun c τ hτ _ => hfam_Top8 hn c hτ) (Wd8_prob hn)
  obtain ⟨cV, hv0, hv, h⟩ := frameGV_at_Top8 hn hk (J := n) hm (hp.trans (charge_Top8 hn))
    (by
      rintro ⟨W, A₁, A₂⟩ hx
      exact (hA_Top8 hn hpos hwd W A₁ A₂ hx).1) hpos
    (fun W A₁ A₂ hx => (hA_Top8 hn hpos hwd W A₁ A₂ hx).2.1)
    (fun W A₁ A₂ hx => (hA_Top8 hn hpos hwd W A₁ A₂ hx).2.2.1)
    (fun W A₁ A₂ hx => (hA_Top8 hn hpos hwd W A₁ A₂ hx).2.2.2)
  refine le_trans ?_ h
  have ht := total_le_Top8 hn hv0 hv (1105 / 1000000)
  linarith

/-- **The arithmetic program of Part 150 (`J = n` atoms, `k ≥ 100n`) succeeds with probability at
least `96/100` for every `n ≥ 8192`.** -/
theorem theorem5_154_8192 {n k : ℕ} (hn : 8192 ≤ n) (hk : 100 * n ≤ k) :
    96 / 100 ≤ (jointP k n).real
      {p | |(fullProg150 k n n).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} :=
  le_trans (by norm_num) (theorem5_154_8192' hn hk)


end BstLean.Part154
