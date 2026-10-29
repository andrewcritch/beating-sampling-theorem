import BstLean.Part182FrameN
import BstLean.Part185FW
import BstLean.Part185FCtr
import BstLean.Part185FCov
import BstLean.Part181Frame

/-!
# Part 185 (file `FFrame`): the Agent frame constant `2.217/n` (TI-lite `λ = 0.735`) at `n ≥ 17 250`
on the covariance event (copy of Part 182 `Frame21M`)

No proof is left open; no `native_decide` or `axiom` is used. The rational constants were chosen
outside Lean (single-process python); Lean checks every inequality.

Seven pieces of the window `0.46 ≤ θ_in ≤ 0.528` (`framePieceT1725_*`) with `frameA_point3N`:
`N = a = 1.115·1.0206·θ_hi` (event `SXM1725`, file `GW`), the centre tables `centreF1725_*` (file
`FCtr`), Part 160's `e_b` tables, and `N_cov` from `cov_TI1725` (file `GCov`). Worst piece
`[0.52, 0.53]`, sum `≈ 2.2170 ≤ 2.217` (piece `[0.52, 0.53]`... see the statements). **`frameA_T_17250`**: `FRAME_A_hyp D (2.217/n)` on
`EA16 ∩ SXM1725 ∩ SSc ∩ SScU ∩ SD' ∩ SCovT1725`.
-/

namespace BstLean.Part183.F1725

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (eDir)
open BstLean.Part153 (XiS Xi4)
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part182

variable {n : ℕ}

/-- The piece `46/100 ≤ θ_in ≤ 47 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_46 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (1773 / 5000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_46 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_46 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_46 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (47 / 100))
    (Ncov := 1773 / 5000)
    (a := 1115 / 1000 * (10206 / 10000) * (47 / 100))
    (eb := 3657 / 5000) (xi := 421 / 5000) (e1 := 8553 / 10000) (e2 := 221 / 100000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (47 / 100)) / 17250)
    (sd := 199 / 500) (s := 5123 / 10000) (r := 299 / 250) (η := 19 / 100) (κ := 403 / 125)
    (ρ := 557 / 100000) (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 5707 / 10000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (47 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (5123 / 10000 - 199 / 500) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (47 / 100)) : ℝ) ^ 4 /
        (17250 ^ 3 * (5123 / 10000 - 199 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_47 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 47 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3621 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_47 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_47 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_47 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (48 / 100))
    (Ncov := 3621 / 10000)
    (a := 1115 / 1000 * (10206 / 10000) * (48 / 100))
    (eb := 454 / 625) (xi := 171 / 2000) (e1 := 8523 / 10000) (e2 := 223 / 100000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (48 / 100)) / 17250)
    (sd := 401 / 1000) (s := 1293 / 2500) (r := 6107 / 5000) (η := 19 / 100) (κ := 329 / 100)
    (ρ := 563 / 100000) (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 23 / 40)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (48 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1293 / 2500 - 401 / 1000) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (48 / 100)) : ℝ) ^ 4 /
        (17250 ^ 3 * (1293 / 2500 - 401 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_48 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 48 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3697 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_48 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_48 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_48 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (49 / 100))
    (Ncov := 3697 / 10000)
    (a := 1115 / 1000 * (10206 / 10000) * (49 / 100))
    (eb := 1443 / 2000) (xi := 867 / 10000) (e1 := 1699 / 2000) (e2 := 9 / 4000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (49 / 100)) / 17250)
    (sd := 81 / 200) (s := 2609 / 5000) (r := 12469 / 10000) (η := 19 / 100) (κ := 1677 / 500)
    (ρ := 569 / 100000) (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 362 / 625)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (49 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (2609 / 5000 - 81 / 200) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (49 / 100)) : ℝ) ^ 4 /
        (17250 ^ 3 * (2609 / 5000 - 81 / 200) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_49 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 49 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (943 / 2500))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_49 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_49 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_49 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (50 / 100))
    (Ncov := 943 / 2500)
    (a := 1115 / 1000 * (10206 / 10000) * (50 / 100))
    (eb := 3583 / 5000) (xi := 11 / 125) (e1 := 4233 / 5000) (e2 := 113 / 50000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (50 / 100)) / 17250)
    (sd := 51 / 125) (s := 1053 / 2000) (r := 12723 / 10000) (η := 19 / 100) (κ := 171 / 50)
    (ρ := 23 / 4000) (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 729 / 1250)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (50 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1053 / 2000 - 51 / 125) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (50 / 100)) : ℝ) ^ 4 /
        (17250 ^ 3 * (1053 / 2000 - 51 / 125) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_50 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 50 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (481 / 1250))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_50 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_50 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_50 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (51 / 100))
    (Ncov := 481 / 1250)
    (a := 1115 / 1000 * (10206 / 10000) * (51 / 100))
    (eb := 3559 / 5000) (xi := 223 / 2500) (e1 := 8437 / 10000) (e2 := 57 / 25000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (51 / 100)) / 17250)
    (sd := 103 / 250) (s := 5311 / 10000) (r := 6489 / 5000) (η := 19 / 100) (κ := 697 / 200)
    (ρ := 581 / 100000) (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 5873 / 10000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (51 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (5311 / 10000 - 103 / 250) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (51 / 100)) : ℝ) ^ 4 /
        (17250 ^ 3 * (5311 / 10000 - 103 / 250) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_51 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 51 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3923 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_51 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_51 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_51 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (52 / 100))
    (Ncov := 3923 / 10000)
    (a := 1115 / 1000 * (10206 / 10000) * (52 / 100))
    (eb := 707 / 1000) (xi := 903 / 10000) (e1 := 8409 / 10000) (e2 := 229 / 100000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (52 / 100)) / 17250)
    (sd := 83 / 200) (s := 1071 / 2000) (r := 827 / 625) (η := 19 / 100) (κ := 3549 / 1000)
    (ρ := 293 / 50000) (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 5913 / 10000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (52 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1071 / 2000 - 83 / 200) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (52 / 100)) : ℝ) ^ 4 /
        (17250 ^ 3 * (1071 / 2000 - 83 / 200) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 528 / 1000`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceT1725_52 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 52 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (249 / 625))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      2217 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (17250 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM1725 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := eb16_sharp_52 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_52 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF1725_52 (by omega) hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 17250 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1115 / 1000 * (10206 / 10000) * (528 / 1000))
    (Ncov := 249 / 625)
    (a := 1115 / 1000 * (10206 / 10000) * (528 / 1000))
    (eb := 3511 / 5000) (xi := 911 / 10000) (e1 := 419 / 500) (e2 := 23 / 10000)
    (N22 := 18334 / 1000 / 17250) (q := 2 * (1115 / 1000 * (10206 / 10000) * (528 / 1000)) / 17250)
    (sd := 419 / 1000) (s := 27 / 50) (r := 3359 / 2500) (η := 19 / 100) (κ := 18 / 5)
    (ρ := 591 / 100000) (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 372 / 625)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (528 / 1000)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (27 / 50 - 419 / 1000) ^ 8) ≤
      (1609 / 100 * (1115 / 1000 * (10206 / 10000) * (528 / 1000)) : ℝ) ^ 4 /
        (17250 ^ 3 * (27 / 50 - 419 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The Agent frame bound `(204/100)/n`, every `n ≥ 22 000`, on the covariance event**: seven
pieces of the window `0.46 ≤ θ_in ≤ 0.528`; on `EA16 D` and the five events `SXM1725`, `SSc`,
`SScU`, `SD'`, `SCovT1725` (Part 181's four and the covariance event of this part). -/
theorem frameA_T_17250 (hn : 17250 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : ∀ c ∈ E, 0 < D.tau0 c ∧ 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) ∧
      thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXM1725 n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n))
    (hE7 : E ⊆ agentEv D (SCovT1725 n)) : FRAME_A_hyp D (2217 / 1000 / n) E := by
  intro c hc w
  obtain ⟨hτ, hlo46, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM1725 n := hE1 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hE4 hc hτ
  have hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hE5 hc hτ
  have hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n := hE6 hc hτ
  have hCv : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT1725 n := hE7 hc hτ
  by_cases h46 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100
  · exact framePieceT1725_46 hn D hD c hτ hlo46 h46 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 47 / 100) (le_trans (by norm_num) hlo46) h46 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePieceT1725_47 hn D hD c hτ hlo47 h47 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 48 / 100) (le_trans (by norm_num) hlo47) h47 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePieceT1725_48 hn D hD c hτ hlo48 h48 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 49 / 100) (le_trans (by norm_num) hlo48) h48 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePieceT1725_49 hn D hD c hτ hlo49 h49 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 50 / 100) (le_trans (by norm_num) hlo49) h49 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePieceT1725_50 hn D hD c hτ hlo50 h50 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 51 / 100) (le_trans (by norm_num) hlo50) h50 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePieceT1725_51 hn D hD c hτ hlo51 h51 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 52 / 100) (le_trans (by norm_num) hlo51) h51 (by norm_num) hX hCv
        (by norm_num)) w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  exact framePieceT1725_52 hn D hD c hτ hlo52 hθ1 hG hX hSS hSU hSD
      (cov_TI1725 hn D c hτ (θh := 528 / 1000) (le_trans (by norm_num) hlo52) hθ1 (by norm_num) hX hCv
        (by norm_num)) w

end BstLean.Part183.F1725

open BstLean.Part183.F1725 in
#print axioms frameA_T_17250
