import BstLean.Part165All

/-!
# Part 174 (file `Root`): the root sum and the mass at `n ≥ 57 000`

No proof is left open; no `native_decide` or `axiom` is used.

A copy of Part 173's file `Root59` (59 000 chain) for `n ≥ 57 000`, namespace
`BstLean.Part174.N57`; names ending in `59` now end in `57`.

* `rc_price57`, `rc_B57`, `rc_R1_57`, `rc_Dp57`, **`root_core57`**: Part 165's root-sum lemmas with
  `g² ≤ 2/57 000` and the mass budget `β_low ≤ 2.01·10⁻¹¹` (Part 173: `2/59 000`, `1.1·10⁻¹¹`).
  `B ≤ 2.014·10⁻¹¹`. The three terms are now `747 + 635 + 701 ≤ 2159` (units `10⁻⁶`; Part 173:
  `722 + 470 + 592`).
* `rootFL_fixed57`, `classifier_paper_root_gen57`, `betaM_4691_57` (`≤ 2.01·10⁻¹¹` at
  `sd = 0.4691`, every `n ≥ 57 000`), **`classifier_paper_root57k`**: Part 165's
  `classifier_paper_root80k` at `n ≥ 57 000`, with the same hypotheses.
-/

namespace BstLean.Part174.N57

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper cLS kLSs gmom gmom_even LatMom)
open BstLean.Part162 (tK tK_nonneg priceC Bpap Dpap cVw cEw iotaP c2η c3η)
open BstLean.Part164 (goodA hE8_of_good CAn E0 E0_nonneg CAn_le E0_le)

section core2

variable {g s : ℝ}

lemma rc_price57 {n : ℕ} {κ L ε E A D e4 d4 e6 d6 : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 57000) (h0κ : 0 ≤ κ) (h0L : 0 ≤ L) (h0ε : 0 ≤ ε) (h0E : 0 ≤ E)
    (h0A : 0 ≤ A) (h0D : 0 ≤ D) (h0e4 : 0 ≤ e4) (h0d4 : 0 ≤ d4) (h0e6 : 0 ≤ e6) (h0d6 : 0 ≤ d6)
    (hκ : κ ≤ 1000203 / 1000000) (hL : L ≤ 12666 / 100 * g) (hε : ε ≤ 1421 / 100000)
    (hE : E ≤ 55) (hA : A ≤ 1776 / 100 * (g ^ 2) ^ 2) (hD : D ≤ 10567 / 1000 * g ^ 2)
    (he4 : e4 ≤ 1199 / 100 * g ^ 2) (hd4 : d4 ≤ 924 / 100 * g) (he6 : e6 ≤ 1449 / 100 * g ^ 2)
    (hd6 : d6 ≤ 1116 / 100 * g) :
    √(priceC κ n L ε E A D e4 d4 e6 d6) ≤ 747 / 10 ^ 6 := by
  have h1 := priceC_mono h0κ (Nat.cast_nonneg n) h0L h0ε h0E h0A h0D h0e4 h0d4 h0e6 h0d6 hκ hL hε
    hE hA hD he4 hd4 he6 hd6
  rw [priceC_scale hg hgn (by norm_num) (by norm_num)] at h1
  have hs : √((1776 / 100 : ℝ) * (10567 / 1000)) ≤ 1370 / 100 :=
    sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs0 : 0 ≤ √((1776 / 100 : ℝ) * (10567 / 1000)) := Real.sqrt_nonneg _
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  have hg0' : g ^ 2 ≤ 2 / 23000 := hg0.trans (by norm_num)
  have hF : (1000203 / 1000000 : ℝ) * g ^ 2 * ((1776 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
        (1776 / 100) * (10567 / 1000)) +
      (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
        √((1776 / 100 : ℝ) * (10567 / 1000)) * g ^ 2)) ^ 2 / 2 +
      g ^ 2 * (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
        √((1776 / 100 : ℝ) * (10567 / 1000)) * g ^ 2)) *
        (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 * (924 / 100) *
          (1199 / 100) * g ^ 2)) ^ 2 / 6 +
      (g ^ 2) ^ 2 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 *
        (924 / 100) * (1199 / 100) * g ^ 2)) ^ 4 / 24 +
      (g ^ 2) ^ 3 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 *
        (924 / 100) * (1199 / 100) * g ^ 2)) ^ 2 *
        (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 + 12666 / 100 * (1116 / 100) *
          (1449 / 100) * g ^ 2)) ^ 3 / 120 +
      55 * (g ^ 2) ^ 4 * (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 +
        12666 / 100 * (1116 / 100) * (1449 / 100) * g ^ 2)) ^ 6 / 720 ≤ 452 := by
    calc _ ≤ (1000203 / 1000000 : ℝ) * (2 / 23000) * ((1776 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
            (1776 / 100) * (10567 / 1000)) +
          (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 * (1370 / 100) *
            (2 / 23000))) ^ 2 / 2 +
          (2 / 23000) * (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
            (1370 / 100) * (2 / 23000))) *
            (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 * (924 / 100) *
              (1199 / 100) * (2 / 23000))) ^ 2 / 6 +
          (2 / 23000) ^ 2 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 +
            12666 / 100 * (924 / 100) * (1199 / 100) * (2 / 23000))) ^ 4 / 24 +
          (2 / 23000) ^ 3 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 +
            12666 / 100 * (924 / 100) * (1199 / 100) * (2 / 23000))) ^ 2 *
            (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 + 12666 / 100 *
              (1116 / 100) * (1449 / 100) * (2 / 23000))) ^ 3 / 120 +
          55 * (2 / 23000) ^ 4 * (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 +
            12666 / 100 * (1116 / 100) * (1449 / 100) * (2 / 23000))) ^ 6 / 720 := by
          gcongr
      _ ≤ 452 := by norm_num
  have h2 : priceC κ n L ε E A D e4 d4 e6 d6 ≤ (g ^ 2) ^ 2 * 452 :=
    h1.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  calc √(priceC κ n L ε E A D e4 d4 e6 d6) ≤ √((g ^ 2) ^ 2 * 452) := Real.sqrt_le_sqrt h2
    _ = g ^ 2 * √452 := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
    _ ≤ (2 / 57000) * (2127 / 100) := by
        gcongr
        exact sqrt_le_of_sq (by norm_num) (by norm_num)
    _ ≤ 747 / 10 ^ 6 := by norm_num

lemma rc_B57 {tlq tsq βl : ℝ} (hg : 0 < g) (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g)) (h0β : 0 ≤ βl)
    (hβ : βl ≤ 201 / 10 ^ 13) :
    0 ≤ Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ∧
    Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ≤ 2014 / 10 ^ 14 := by
  unfold Bpap
  have hu : 0 < g ^ 2 := by positivity
  have h1 : tlq / (22 * g ^ 2) ≤ 53493 / 10000 / 22 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : tsq / (35 / 2 * (g ^ 2 * g)) ≤ 42768 / 10000 / (35 / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_pos hu hg]
  have h10 : 0 ≤ tlq / (22 * g ^ 2) := by positivity
  have h20 : 0 ≤ tsq / (35 / 2 * (g ^ 2 * g)) := by positivity
  refine ⟨by positivity, ?_⟩
  calc (tlq / (22 * g ^ 2)) ^ (2 * 12) + (tsq / (35 / 2 * (g ^ 2 * g))) ^ (2 * 12) + βl
      ≤ (53493 / 10000 / 22) ^ (2 * 12) + (42768 / 10000 / (35 / 2)) ^ (2 * 12) + 201 / 10 ^ 13 := by
        gcongr
    _ ≤ 2014 / 10 ^ 14 := by norm_num

lemma rc_R1_57 {B : ℝ} (h0B : 0 ≤ B) (hB : B ≤ 2014 / 10 ^ 14) :
    √(2 * (1 + (1 / 10000 : ℝ)⁻¹) * B) ≤ 635 / 10 ^ 6 := by
  apply sqrt_le_of_sq (by norm_num)
  calc 2 * (1 + (1 / 10000 : ℝ)⁻¹) * B ≤ 2 * (1 + (1 / 10000 : ℝ)⁻¹) * (2014 / 10 ^ 14) := by gcongr
    _ ≤ (635 / 10 ^ 6) ^ 2 := by norm_num

lemma rc_Dp57 {n : ℕ} {B CA Vl VS : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 57000) (hs : 43 / 100 ≤ s) (h0B : 0 ≤ B) (hB : B ≤ 2014 / 10 ^ 14)
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000) (h0Vl : 0 ≤ Vl)
    (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 4247 / 10 * (g ^ 2) ^ 4) :
    √(Dpap n B CA Vl VS (1 / 10000) (g * s)) ≤ 701 / 10 ^ 6 := by
  unfold Dpap
  have hn' : (n : ℝ) = 2 / g ^ 2 := by field_simp; linarith
  have hsB : √B ≤ 4488 / 10 ^ 9 := (Real.sqrt_le_sqrt hB).trans
    (sqrt_le_of_sq (by norm_num) (by norm_num))
  have hsB0 : 0 ≤ √B := Real.sqrt_nonneg _
  have hu : 0 < g ^ 2 := by positivity
  have hT1 : CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) ≤
      1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 10000) * (43 / 100) ^ 2) * g ^ 2 := by
    calc CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2)
        ≤ 1532 / 1000 * (127512 / 100000 * (g ^ 2) ^ 2) /
          (2 * (1 - 1 / 10000) * (g * (43 / 100)) ^ 2) := by gcongr
      _ = _ := by field_simp
  have hT2 : (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) ≤
      2 * (4247 / 10) / (8 * (1 - 1 / 10000) ^ 2 * (43 / 100) ^ 4) * g ^ 2 := by
    rw [hn']
    calc 2 / g ^ 2 * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4)
        ≤ 2 / g ^ 2 * (4247 / 10 * (g ^ 2) ^ 4) /
          (8 * (1 - 1 / 10000) ^ 2 * (g * (43 / 100)) ^ 4) := by gcongr
      _ = _ := by field_simp
  have hsum : CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) ≤ 3112 * g ^ 2 := by
    have e : 1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 10000) * (43 / 100) ^ 2) +
        2 * (4247 / 10) / (8 * (1 - 1 / 10000) ^ 2 * (43 / 100) ^ 4) ≤ (3112 : ℝ) := by norm_num
    nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : 0 ≤ CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) := by positivity
  apply sqrt_le_of_sq (by norm_num)
  calc √B * (CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
        (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4))
      ≤ 4488 / 10 ^ 9 * (3112 * (2 / 57000)) := by
        gcongr
        exact hsum.trans (by gcongr)
    _ ≤ (701 / 10 ^ 6) ^ 2 := by norm_num

theorem root_core57 {n : ℕ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2) (hg0 : g ^ 2 ≤ 2 / 57000)
    (hs : 43 / 100 ≤ s) {CA Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl : ℝ}
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000)
    (h0Vs : 0 ≤ Vs) (hVs : Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3)
    (h0Vl : 0 ≤ Vl) (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 4247 / 10 * (g ^ 2) ^ 4)
    (h0ts8 : 0 ≤ ts8) (hts8 : ts8 ≤ 25379 / 10000 * (g ^ 2 * g))
    (h0tl8 : 0 ≤ tl8) (htl8 : tl8 ≤ 31743 / 10000 * g ^ 2)
    (h0ts12 : 0 ≤ ts12) (hts12 : ts12 ≤ 30661 / 10000 * (g ^ 2 * g))
    (h0tl12 : 0 ≤ tl12) (htl12 : tl12 ≤ 38350 / 10000 * g ^ 2)
    (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g))
    (h0β : 0 ≤ βl) (hβ : βl ≤ 201 / 10 ^ 13) :
    rootE n (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) (1 / 10000) CA (g * s)
      Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl ≤ 2159 / 10 ^ 6 := by
  have hg0' : g ^ 2 ≤ 2 / 23000 := hg0.trans (by norm_num)
  obtain ⟨-, hε0, hε1⟩ := rc_eps hg hg0' hs
  obtain ⟨hκd, hκ1⟩ := rc_kappa hε0 hε1
  have hκ0 := (inv_pos.2 hκd).le
  obtain ⟨hL0, hL1⟩ := rc_L hg hs h0CA hCA
  have hnε := rc_neps (n := n) hg hgn hg0' hs
  have hEE := rc_EE hg hg0' hκ0 hκ1 hε0 hε1 hnε hL0 hL1
  obtain ⟨hA0, hA⟩ := rc_A hg hg0' hs h0Vs hVs
  obtain ⟨hD0, hD⟩ := rc_D hg hs h0CA hCA h0Vl hVl
  obtain ⟨he40, he4⟩ := rc_e (p := 8) hg hg0' hs (by norm_num) h0ts8 hts8
  obtain ⟨he60, he6⟩ := rc_e (p := 12) hg hg0' hs (by norm_num) h0ts12 hts12
  obtain ⟨hd40, hd4⟩ := rc_d (p := 8) hg hs h0CA hCA (by norm_num) h0tl8 htl8
  obtain ⟨hd60, hd6⟩ := rc_d (p := 12) hg hs h0CA hCA (by norm_num) h0tl12 htl12
  have hP := rc_price57 (n := n) hg hgn hg0 hκ0 hL0 hε0 (exp_pos _).le hA0 hD0 he40 hd40 he60 hd60
    hκ1 hL1 hε1 hEE hA hD (he4.trans (by gcongr; norm_num)) (hd4.trans (by gcongr; norm_num))
    (he6.trans (by gcongr; norm_num)) (hd6.trans (by gcongr; norm_num))
  obtain ⟨hB0, hB⟩ := rc_B57 hg h0tlq htlq h0tsq htsq h0β hβ
  have hR1 := rc_R1_57 hB0 hB
  have hR3 := rc_Dp57 (n := n) hg hgn hg0 hs hB0 hB h0CA hCA h0Vl hVl h0VS hVS
  unfold rootE
  linarith

end core2

variable {n : ℕ}

theorem rootFL_fixed57 (hn : 57000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd)
    (hβ : BstLean.Part165.betaM n sd ≤ 201 / 10 ^ 13) (D : Design n) (c : Ret n)
    (hCL : (0 : ℝ) < 51 / 10) (hCS : (0 : ℝ) < 326 / 100 * (2 / n))
    (hL12 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12)
    (hS12 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12)
    (hE8 : ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E0 n ^ 8)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < √(2 / (n : ℝ)) * sd}
      ∂muI n ≤ BstLean.Part165.betaM n sd) :
    rootFL (22 * √(2 / (n : ℝ)) ^ 2) (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (1 / 10000)
      (CAn n) (latMomOfPsi12e (by omega) D c hCL hCS (E0_nonneg n) (betaM_nonneg n sd)
        hL12 hS12 hE8 hmass) ≤ 2159 / 10 ^ 6 := by
  have hnR : (57000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set g := √(2 / (n : ℝ)) with hgdef
  have hg2 : g ^ 2 = 2 / n := Real.sq_sqrt (by positivity)
  have hg : 0 < g := Real.sqrt_pos.mpr (by positivity)
  have hgn : (n : ℝ) * g ^ 2 = 2 := by rw [hg2]; field_simp
  have hg0 : g ^ 2 ≤ 2 / 57000 := by
    rw [hg2]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  set P := latMomOfPsi12e (by omega) D c hCL hCS (E0_nonneg n) (betaM_nonneg n sd)
    hL12 hS12 hE8 hmass with hP
  -- the two square roots
  have hCSn : √(326 / 100 * (2 / (n : ℝ)) / n) = √(163 / 100) * g ^ 2 := by
    rw [hg2, show 326 / 100 * (2 / (n : ℝ)) / n = 163 / 100 * (2 / n) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hCLn : √(51 / 10 / (n : ℝ)) = √(255 / 100) * g := by
    rw [hgdef, ← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hs1 : √(163 / 100 : ℝ) ≤ 1276715 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs2 : √(255 / 100 : ℝ) ≤ 1596872 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs10 : 0 ≤ √(163 / 100 : ℝ) := Real.sqrt_nonneg _
  have hs20 : 0 ≤ √(255 / 100 : ℝ) := Real.sqrt_nonneg _
  -- the factors `kLSs`
  have hk4 : kLSs n 4 ≤ 198779 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS4_le (by norm_num) (by norm_num)
  have hk6 : kLSs n 6 ≤ 240152 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS6_le (by norm_num) (by norm_num)
  have hk12 : kLSs n 12 ≤ 334984 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS12_le (by norm_num) (by norm_num)
  have hk40 : 0 ≤ kLSs n 4 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk60 : 0 ≤ kLSs n 6 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk120 : 0 ≤ kLSs n 12 :=
    (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  -- the fields
  have fS : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1276715 / 1000000) ≤ M →
      k * √(326 / 100 * (2 / (n : ℝ)) / n) ≤ M * (g ^ 2 * g) := by
    intro k K hk0 hk M hM
    rw [hCSn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(163 / 100) * g ^ 2) ≤ (K * g) * (1276715 / 1000000 * g ^ 2) := by gcongr
      _ = K * (1276715 / 1000000) * (g ^ 2 * g) := by ring
      _ ≤ M * (g ^ 2 * g) := by gcongr
  have fL : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1596872 / 1000000) ≤ M →
      k * √(51 / 10 / (n : ℝ)) ≤ M * g ^ 2 := by
    intro k K hk0 hk M hM
    rw [hCLn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(255 / 100) * g) ≤ (K * g) * (1596872 / 1000000 * g) := by gcongr
      _ = K * (1596872 / 1000000) * g ^ 2 := by ring
      _ ≤ M * g ^ 2 := by gcongr
  have hts8 : P.ts8 ≤ 25379 / 10000 * (g ^ 2 * g) := fS hk40 hk4 (by norm_num)
  have hts12 : P.ts12 ≤ 30661 / 10000 * (g ^ 2 * g) := fS hk60 hk6 (by norm_num)
  have htsq : P.tsq ≤ 42768 / 10000 * (g ^ 2 * g) := fS hk120 hk12 (by norm_num)
  have htl8 : P.tl8 ≤ 31743 / 10000 * g ^ 2 := fL hk40 hk4 (by norm_num)
  have htl12 : P.tl12 ≤ 38350 / 10000 * g ^ 2 := fL hk60 hk6 (by norm_num)
  have htlq : P.tlq ≤ 53493 / 10000 * g ^ 2 := fL hk120 hk12 (by norm_num)
  have hVs : P.Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3 := by
    change 326 / 100 * (2 / (n : ℝ)) / n / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 81508 / 100000 * (2 / (n : ℝ)) ^ 3 * (n - 2) = 652064 / 100000 * (n - 2) / n ^ 3 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 326 / 100 * (2 / (n : ℝ)) / n * n ^ 3 = 652 / 100 * n := by field_simp; ring
    rw [e2]
    nlinarith
  have hVl : P.Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2 := by
    change 51 / 10 / (n : ℝ) / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 127512 / 100000 * (2 / (n : ℝ)) ^ 2 * (n - 2) = 510048 / 100000 * (n - 2) / n ^ 2 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 51 / 10 / (n : ℝ) * n ^ 2 = 51 / 10 * n := by field_simp
    rw [e2]
    nlinarith
  have hVS : P.VS ≤ 4247 / 10 * (g ^ 2) ^ 4 := by
    change 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E0 n ^ 2 ≤ _
    have h1 := fS hk40 hk4 (M := 25379 / 10000) (by norm_num)
    have h10 : 0 ≤ kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n) := by positivity
    have h2 := E0_le (by omega : 23000 ≤ n)
    rw [← hgdef] at h2
    calc 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E0 n ^ 2
        ≤ 4 * (25379 / 10000 * (g ^ 2 * g)) ^ 2 * (406 / 100 * g) ^ 2 := by
          gcongr
          exact E0_nonneg n
      _ = 4 * (25379 / 10000) ^ 2 * (406 / 100) ^ 2 * (g ^ 2) ^ 4 := by ring
      _ ≤ 4247 / 10 * (g ^ 2) ^ 4 := by gcongr; norm_num
  have hβ' : P.βlow ≤ 201 / 10 ^ 13 := hβ
  have hCA := CAn_le (by omega : 23000 ≤ n)
  have hCA0 : 0 ≤ CAn n := by unfold CAn BstLean.Part164.chiUp; positivity
  exact root_core57 hg hgn hg0 hsd hCA0 hCA P.hVs0 hVs P.hVl0 hVl P.hVS0 hVS P.hts8.le hts8 P.htl8.le
    htl8 P.hts12.le hts12 P.htl12.le htl12 P.htlq htlq P.htsq htsq P.hβl hβ'

theorem classifier_paper_root_gen57 (hn : 57000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd)
    (hsd' : sd < s0) (hβ : BstLean.Part165.betaM n sd ≤ 201 / 10 ^ 13) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw) EA,
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * sd)
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : (57000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsd0 : 0 < sd := lt_of_lt_of_le (by norm_num) hsd
  refine classifier_paper_free23_mass40 (by omega) fT wT hf hw t hEA hA hroom fun c hc => ?_
  obtain ⟨hL12, hS12, hbias⟩ := hM c hc
  have hCS : (0 : ℝ) < 326 / 100 * (2 / n) := by positivity
  refine ⟨22 * √(2 / (n : ℝ)) ^ 2, 35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ))), sd,
    1 / 10000, 51 / 10, 326 / 100 * (2 / n), by norm_num, by norm_num, by norm_num, hCS,
    hsd0, hsd', hL12, hS12, by positivity, by positivity, eps0_fixed_lt (by omega) hsd, ?_, hbias⟩
  exact rootFL_fixed57 hn hsd hβ _ c (by norm_num) hCS hL12 hS12 _ _

theorem betaM_4691_57 (hn : 57000 ≤ n) : BstLean.Part165.betaM n (4691 / 10000) ≤ 201 / 10 ^ 13 := by
  have hnR : (57000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold BstLean.Part165.betaM s0
  rw [gmom_40]
  have h1 : (π / 2) ^ 40 ≤ (15708 / 10000 : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) pi_half_le 40
  have h2 : 706 / 1000 / ((n : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2) ≤
      706 / 1000 / ((57000 : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  have h3 := pow_le_pow_left₀ (by positivity) h2 20
  calc (π / 2) ^ 40 * 319830986772877770815625 *
        (706 / 1000 / ((n : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2)) ^ 20
      ≤ (15708 / 10000 : ℝ) ^ 40 * 319830986772877770815625 *
        (706 / 1000 / ((57000 : ℝ) * (5087 / 10000 - 4691 / 10000) ^ 2)) ^ 20 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) h3 (by positivity)
          (by positivity)
    _ ≤ 201 / 10 ^ 13 := by norm_num

theorem classifier_paper_root57k (hn : 57000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw) EA,
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_root_gen57 hn (by norm_num) (by unfold s0; norm_num)
    (betaM_4691_57 hn) fT wT hf hw t hEA hA hroom hM

end BstLean.Part174.N57
