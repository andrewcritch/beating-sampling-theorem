import BstLean.Part182FrameN
import BstLean.Part181Frame

/-!
# Part 182 (file `Frame`): the Agent frame constant `1.82/n` at `n ≥ 22 000`, GIVEN the covariance

No proof is left open; no `native_decide` or `axiom` is used. The rational constants were chosen
outside Lean (a single-process python calculator); Lean checks every inequality.

The seven pieces of Part 181 (`framePiece22_*`), with `frameA_point3N` in place of
`frameA_point3`: the main term uses the covariance constant `N_cov` of the hypothesis
`COV_at D c N_cov` (supplied by the Schur certificate, file `Cov`), and all other constants are
Part 181's. `N_cov = 0.582·1.0182·θ_hi + 1.1·1.0182·θ_hi·0.0036` (rounded up). Worst piece
`[0.51, 0.52]`, sum `≈ 1.8145 ≤ 1.82`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (eDir)
open BstLean.Part153 (XiS Xi4)
open BstLean.Part156 BstLean.Part160 BstLean.Part181

variable {n : ℕ}

/-- The piece `46/100 ≤ θ_in ≤ 47 / 100`: `N = a = 1.1·1.0182·47 / 100`, `N_cov = 561 / 2000`, `ξ = 803/10000`,
`3401/5000 ≤ e_b ≤ 3657/5000`, `s = 1283/2500`, `sd = 203/500`. -/
lemma framePieceT_46 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (561 / 2000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_46 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_46 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_46 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (47 / 100))
    (Ncov := 561 / 2000)
    (a := 11 / 10 * (10182 / 10000) * (47 / 100))
    (eb := 3657 / 5000) (xi := 803 / 10000) (e1 := 8553 / 10000) (e2 := 6 / 3125)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (47 / 100)) / 22000)
    (sd := 203 / 500) (s := 1283 / 2500) (r := 11771 / 10000) (η := 19 / 100) (κ := 3157 / 1000)
    (ρ := 49 / 10000) (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 5699 / 10000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (47 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1283 / 2500 - 203 / 500) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (47 / 100)) : ℝ) ^ 4 /
        (22000 ^ 3 * (1283 / 2500 - 203 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48 / 100`: `N = a = 1.1·1.0182·48 / 100`, `N_cov = 179 / 625`, `ξ = 815/10000`,
`6753/10000 ≤ e_b ≤ 454/625`, `s = 2591/5000`, `sd = 409/1000`. -/
lemma framePieceT_47 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 47 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (179 / 625))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_47 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_47 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_47 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (48 / 100))
    (Ncov := 179 / 625)
    (a := 11 / 10 * (10182 / 10000) * (48 / 100))
    (eb := 454 / 625) (xi := 815 / 10000) (e1 := 8523 / 10000) (e2 := 193 / 100000)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (48 / 100)) / 22000)
    (sd := 409 / 1000) (s := 2591 / 5000) (r := 6011 / 5000) (η := 19 / 100) (κ := 3221 / 1000)
    (ρ := 99 / 20000) (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 2871 / 5000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (48 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (2591 / 5000 - 409 / 1000) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (48 / 100)) : ℝ) ^ 4 /
        (22000 ^ 3 * (2591 / 5000 - 409 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49 / 100`: `N = a = 1.1·1.0182·49 / 100`, `N_cov = 731 / 2500`, `ξ = 827/10000`,
`1341/2000 ≤ e_b ≤ 1443/2000`, `s = 1307/2500`, `sd = 413/1000`. -/
lemma framePieceT_48 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 48 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (731 / 2500))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_48 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_48 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_48 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (49 / 100))
    (Ncov := 731 / 2500)
    (a := 11 / 10 * (10182 / 10000) * (49 / 100))
    (eb := 1443 / 2000) (xi := 827 / 10000) (e1 := 1699 / 2000) (e2 := 97 / 50000)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (49 / 100)) / 22000)
    (sd := 413 / 1000) (s := 1307 / 2500) (r := 767 / 625) (η := 19 / 100) (κ := 657 / 200)
    (ρ := 1 / 200) (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 5783 / 10000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (49 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1307 / 2500 - 413 / 1000) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (49 / 100)) : ℝ) ^ 4 /
        (22000 ^ 3 * (1307 / 2500 - 413 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50 / 100`: `N = a = 1.1·1.0182·50 / 100`, `N_cov = 373 / 1250`, `ξ = 839/10000`,
`6657/10000 ≤ e_b ≤ 3583/5000`, `s = 2637/5000`, `sd = 417/1000`. -/
lemma framePieceT_49 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 49 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (373 / 1250))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_49 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_49 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_49 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (50 / 100))
    (Ncov := 373 / 1250)
    (a := 11 / 10 * (10182 / 10000) * (50 / 100))
    (eb := 3583 / 5000) (xi := 839 / 10000) (e1 := 4233 / 5000) (e2 := 49 / 25000)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (50 / 100)) / 22000)
    (sd := 417 / 1000) (s := 2637 / 5000) (r := 12523 / 10000) (η := 19 / 100) (κ := 3349 / 1000)
    (ρ := 101 / 20000) (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 364 / 625)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (50 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (2637 / 5000 - 417 / 1000) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (50 / 100)) : ℝ) ^ 4 /
        (22000 ^ 3 * (2637 / 5000 - 417 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51 / 100`: `N = a = 1.1·1.0182·51 / 100`, `N_cov = 3043 / 10000`, `ξ = 851/10000`,
`661/1000 ≤ e_b ≤ 3559/5000`, `s = 133/250`, `sd = 21/50`. -/
lemma framePieceT_50 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 50 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3043 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_50 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_50 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_50 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (51 / 100))
    (Ncov := 3043 / 10000)
    (a := 11 / 10 * (10182 / 10000) * (51 / 100))
    (eb := 3559 / 5000) (xi := 851 / 10000) (e1 := 8437 / 10000) (e2 := 197 / 100000)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (51 / 100)) / 22000)
    (sd := 21 / 50) (s := 133 / 250) (r := 12773 / 10000) (η := 19 / 100) (κ := 3413 / 1000)
    (ρ := 51 / 10000) (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 1173 / 2000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (51 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (133 / 250 - 21 / 50) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (51 / 100)) : ℝ) ^ 4 /
        (22000 ^ 3 * (133 / 250 - 21 / 50) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52 / 100`: `N = a = 1.1·1.0182·52 / 100`, `N_cov = 3103 / 10000`, `ξ = 862/10000`,
`6563/10000 ≤ e_b ≤ 707/1000`, `s = 1073/2000`, `sd = 53/125`. -/
lemma framePieceT_51 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 51 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3103 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_51 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_51 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_51 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (52 / 100))
    (Ncov := 3103 / 10000)
    (a := 11 / 10 * (10182 / 10000) * (52 / 100))
    (eb := 707 / 1000) (xi := 862 / 10000) (e1 := 8409 / 10000) (e2 := 99 / 50000)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (52 / 100)) / 22000)
    (sd := 53 / 125) (s := 1073 / 2000) (r := 814 / 625) (η := 19 / 100) (κ := 3477 / 1000)
    (ρ := 103 / 20000) (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 1181 / 2000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (52 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1073 / 2000 - 53 / 125) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (52 / 100)) : ℝ) ^ 4 /
        (22000 ^ 3 * (1073 / 2000 - 53 / 125) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 528 / 1000`: `N = a = 1.1·1.0182·528 / 1000`, `N_cov = 3151 / 10000`, `ξ = 874/10000`,
`6517/10000 ≤ e_b ≤ 3511/5000`, `s = 5409/10000`, `sd = 427/1000`. -/
lemma framePieceT_52 (hn : 22000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 52 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM22 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3151 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      182 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM22 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_52 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_52 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_52 (by omega) hτ hθ0 (hθ1.trans (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 22000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 11 / 10 * (10182 / 10000) * (528 / 1000))
    (Ncov := 3151 / 10000)
    (a := 11 / 10 * (10182 / 10000) * (528 / 1000))
    (eb := 3511 / 5000) (xi := 874 / 10000) (e1 := 419 / 500) (e2 := 1 / 500)
    (N22 := 18334 / 1000 / 22000) (q := 2 * (11 / 10 * (10182 / 10000) * (528 / 1000)) / 22000)
    (sd := 427 / 1000) (s := 5409 / 10000) (r := 1653 / 1250) (η := 19 / 100) (κ := 3529 / 1000)
    (ρ := 519 / 100000) (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 1189 / 2000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11 / 10 * (10182 / 10000) * (528 / 1000)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (5409 / 10000 - 427 / 1000) ^ 8) ≤
      (1609 / 100 * (11 / 10 * (10182 / 10000) * (528 / 1000)) : ℝ) ^ 4 /
        (22000 ^ 3 * (5409 / 10000 - 427 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

end BstLean.Part182
