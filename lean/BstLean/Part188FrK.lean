import BstLean.Part187All
import BstLean.Part182FrameN
import BstLean.Part186GW
import BstLean.Part186GCtr
import BstLean.Part186GCov
import BstLean.Part186CovC
import BstLean.Part181Frame
import BstLean.Part188Kap



namespace BstLean.Part188.Frame16384
open BstLean.Part183 BstLean.Part183.F16384

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (eDir)
open BstLean.Part153 (XiS Xi4)
open BstLean.Part156 BstLean.Part160 BstLean.Part181
open BstLean.Part182

variable {n : ℕ}

/-- The piece `46/100 ≤ θ_in ≤ 47 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_46 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (303 / 1000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_46 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_46 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_46 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (47 / 100))
    (Ncov := 303 / 1000)
    (a := 1119 / 1000 * (10211 / 10000) * (47 / 100))
    (eb := 72441 / 100000) (xi := 213 / 2500) (e1 := 532 / 625) (e2 := 229 / 100000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (47 / 100)) / 16384)
    (sd := 201 / 500) (s := 1297 / 2500) (r := 12009 / 10000) (η := 19 / 100) (κ := 1621 / 500)
    (ρ := 573 / 100000) (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 5709 / 10000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (47 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1297 / 2500 - 201 / 500) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (47 / 100)) : ℝ) ^ 4 /
        (16384 ^ 3 * (1297 / 2500 - 201 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_47 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 47 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (307 / 1000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_47 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_47 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_47 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (48 / 100))
    (Ncov := 307 / 1000)
    (a := 1119 / 1000 * (10211 / 10000) * (48 / 100))
    (eb := 4497 / 6250) (xi := 54 / 625) (e1 := 8483 / 10000) (e2 := 23 / 10000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (48 / 100)) / 16384)
    (sd := 81 / 200) (s := 1309 / 2500) (r := 1533 / 1250) (η := 19 / 100) (κ := 3307 / 1000)
    (ρ := 579 / 100000) (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 719 / 1250)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (48 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1309 / 2500 - 81 / 200) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (48 / 100)) : ℝ) ^ 4 /
        (16384 ^ 3 * (1309 / 2500 - 81 / 200) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_48 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 48 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3109 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_48 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_48 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_48 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (49 / 100))
    (Ncov := 3109 / 10000)
    (a := 1119 / 1000 * (10211 / 10000) * (49 / 100))
    (eb := 71467 / 100000) (xi := 877 / 10000) (e1 := 4227 / 5000) (e2 := 29 / 12500)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (49 / 100)) / 16384)
    (sd := 409 / 1000) (s := 2641 / 5000) (r := 313 / 250) (η := 19 / 100) (κ := 843 / 250)
    (ρ := 117 / 20000) (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 2897 / 5000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (49 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (2641 / 5000 - 409 / 1000) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (49 / 100)) : ℝ) ^ 4 /
        (16384 ^ 3 * (2641 / 5000 - 409 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_49 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 49 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3147 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_49 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_49 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_49 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (50 / 100))
    (Ncov := 3147 / 10000)
    (a := 1119 / 1000 * (10211 / 10000) * (50 / 100))
    (eb := 35493 / 50000) (xi := 889 / 10000) (e1 := 4213 / 5000) (e2 := 233 / 100000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (50 / 100)) / 16384)
    (sd := 103 / 250) (s := 5327 / 10000) (r := 511 / 400) (η := 19 / 100) (κ := 3437 / 1000)
    (ρ := 591 / 100000) (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 2917 / 5000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (50 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (5327 / 10000 - 103 / 250) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (50 / 100)) : ℝ) ^ 4 /
        (16384 ^ 3 * (5327 / 10000 - 103 / 250) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_50 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 50 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (199 / 625))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_50 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_50 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_50 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (51 / 100))
    (Ncov := 199 / 625)
    (a := 1119 / 1000 * (10211 / 10000) * (51 / 100))
    (eb := 7051 / 10000) (xi := 901 / 10000) (e1 := 4199 / 5000) (e2 := 47 / 20000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (51 / 100)) / 16384)
    (sd := 83 / 200) (s := 537 / 1000) (r := 13031 / 10000) (η := 19 / 100) (κ := 1751 / 500)
    (ρ := 597 / 100000) (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 47 / 80)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (51 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (537 / 1000 - 83 / 200) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (51 / 100)) : ℝ) ^ 4 /
        (16384 ^ 3 * (537 / 1000 - 83 / 200) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52 / 100`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_51 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 51 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (161 / 500))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_51 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_51 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_51 (by omega) hτ (le_trans (by norm_num) hθ0) (le_trans hθ1 (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (52 / 100))
    (Ncov := 161 / 500)
    (a := 1119 / 1000 * (10211 / 10000) * (52 / 100))
    (eb := 70037 / 100000) (xi := 913 / 10000) (e1 := 8369 / 10000) (e2 := 237 / 100000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (52 / 100)) / 16384)
    (sd := 419 / 1000) (s := 1083 / 2000) (r := 6643 / 5000) (η := 19 / 100) (κ := 3567 / 1000)
    (ρ := 603 / 100000) (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 1183 / 2000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (52 / 100)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (1083 / 2000 - 419 / 1000) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (52 / 100)) : ℝ) ^ 4 /
        (16384 ^ 3 * (1083 / 2000 - 419 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 528 / 1000`: constants of the `n ≥ 21 000` table (see the call). -/
lemma framePieceK16384_52 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 52 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (hcov : COV_at D c (3237 / 10000))
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      1967 / 1000 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi4 := Xi4_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have hXi8 := Xi8_SXM16384 hn hτ hθ0' hθ1 (by norm_num) hX
  have heb := BstLean.Part188.eb16K_52 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_52 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centreF16384_52 (by omega) hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3N (by omega) D hD c hτ (N := 1119 / 1000 * (10211 / 10000) * (528 / 1000))
    (Ncov := 3237 / 10000)
    (a := 1119 / 1000 * (10211 / 10000) * (528 / 1000))
    (eb := 6957 / 10000) (xi := 23 / 250) (e1 := 8341 / 10000) (e2 := 237 / 100000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1119 / 1000 * (10211 / 10000) * (528 / 1000)) / 16384)
    (sd := 211 / 500) (s := 2729 / 5000) (r := 13491 / 10000) (η := 19 / 100) (κ := 1809 / 500)
    (ρ := 607 / 100000) (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 2977 / 5000)
    (by norm_num) (by norm_num) hcov c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (528 / 1000)) : ℝ) ^ 4 /
      ((n : ℝ) ^ 3 * (2729 / 5000 - 211 / 500) ^ 8) ≤
      (1609 / 100 * (1119 / 1000 * (10211 / 10000) * (528 / 1000)) : ℝ) ^ 4 /
        (16384 ^ 3 * (2729 / 5000 - 211 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num


/-- One piece of the two-level core covariance: `COV_at D c N` from `cov_coreP` with `λ₀ = 0.647`,
`K_e = 1.0211`, `M_x = 1.119·1.0211` (events `SXM16384`, `SCovT16384`, `SCovP`). -/
lemma covC_piece (hn : 16384 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {θl θh lam1 N : ℝ}
    (hθl : 46 / 100 ≤ θl) (hθ0 : θl ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ θh)
    (hθh : θh ≤ 528 / 1000) (hl1 : 0 ≤ lam1)
    (hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n)
    (hC : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT16384 n)
    (hP : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ BstLean.Part186.SCovP n θl θh lam1)
    (hN : lam1 * (10211 / 10000) * θh + 647 / 1000 * (100 / 93) * θh * (548 / 100000) +
      1119 / 1000 * (10211 / 10000) * θh * (4933 / 10 ^ 6) ≤ N) :
    COV_at D c N := by
  have hθ0' : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans hθl hθ0
  have hEw : ∫ ξ, BstLean.Part182.wN c.1.2 (D.tau0 c) ξ ∂stdGauss (Fin n) ≤
      10211 / 10000 * (thetaC c.1.2 (D.tau0 c) / n) := by
    have h := Ew_le_F16384 hn c.1.2 hτ hθ0' (hθ1.trans hθh)
    simpa only [BstLean.Part182.wN, integral_const_mul] using h
  have hX4 := Xi4_SXM16384 hn hτ hθ0' hθ1 hθh hX
  have hb0 : badMass n 5 14 8 (647 / 1000) ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ≤
      1 / 10 ^ 13 := by
    rcases hC with h | h
    · exact absurd ⟨hθ0', hθ1.trans hθh⟩ h
    · exact h
  exact BstLean.Part186.cov_coreP hn D c hτ (lam0 := 647 / 1000) (Ke := 10211 / 10000)
    (Mx := 1119 / 1000 * (10211 / 10000)) hθl hθ0 hθ1 hθh hl1 (by norm_num) (by norm_num)
    hEw hX4 hP hb0 hN

/-- **The Agent frame bound `(204/100)/n`, every `n ≥ 22 000`, on the covariance event**: seven
pieces of the window `0.46 ≤ θ_in ≤ 0.528`; on `EA16 D` and the five events `SXM16384`, `SSc`,
`SScU`, `SD'`, `SCovT16384` (Part 181's four and the covariance event of this part). -/
theorem frameA_K_16384 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : ∀ c ∈ E, 0 < D.tau0 c ∧ 46 / 100 ≤ thetaC c.1.2 (D.tau0 c) ∧
      thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXM16384 n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n))
    (hE7 : E ⊆ agentEv D (SCovT16384 n))
    (hP46 : E ⊆ agentEv D (BstLean.Part186.SCovP n (46/100) (47/100) (311/500)))
    (hP47 : E ⊆ agentEv D (BstLean.Part186.SCovP n (47/100) (48/100) (617/1000)))
    (hP48 : E ⊆ agentEv D (BstLean.Part186.SCovP n (48/100) (49/100) (153/250)))
    (hP49 : E ⊆ agentEv D (BstLean.Part186.SCovP n (49/100) (50/100) (607/1000)))
    (hP50 : E ⊆ agentEv D (BstLean.Part186.SCovP n (50/100) (51/100) (301/500)))
    (hP51 : E ⊆ agentEv D (BstLean.Part186.SCovP n (51/100) (52/100) (597/1000)))
    (hP52 : E ⊆ agentEv D (BstLean.Part186.SCovP n (52/100) (528/1000) (591/1000))) :
    FRAME_A_hyp D (1967 / 1000 / n) E := by
  intro c hc w
  obtain ⟨hτ, hlo46, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hX : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM16384 n := hE1 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hE4 hc hτ
  have hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hE5 hc hτ
  have hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n := hE6 hc hτ
  have hCv : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SCovT16384 n := hE7 hc hτ
  by_cases h46 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100
  · exact framePieceK16384_46 hn D hD c hτ hlo46 h46 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 46/100) (θh := 47 / 100) (lam1 := 311/500) (by norm_num) hlo46 h46 (by norm_num)
        (by norm_num) hX hCv (hP46 hc hτ) (by norm_num)) w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePieceK16384_47 hn D hD c hτ hlo47 h47 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 47/100) (θh := 48 / 100) (lam1 := 617/1000) (by norm_num) hlo47 h47 (by norm_num)
        (by norm_num) hX hCv (hP47 hc hτ) (by norm_num)) w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePieceK16384_48 hn D hD c hτ hlo48 h48 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 48/100) (θh := 49 / 100) (lam1 := 153/250) (by norm_num) hlo48 h48 (by norm_num)
        (by norm_num) hX hCv (hP48 hc hτ) (by norm_num)) w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePieceK16384_49 hn D hD c hτ hlo49 h49 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 49/100) (θh := 50 / 100) (lam1 := 607/1000) (by norm_num) hlo49 h49 (by norm_num)
        (by norm_num) hX hCv (hP49 hc hτ) (by norm_num)) w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePieceK16384_50 hn D hD c hτ hlo50 h50 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 50/100) (θh := 51 / 100) (lam1 := 301/500) (by norm_num) hlo50 h50 (by norm_num)
        (by norm_num) hX hCv (hP50 hc hτ) (by norm_num)) w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePieceK16384_51 hn D hD c hτ hlo51 h51 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 51/100) (θh := 52 / 100) (lam1 := 597/1000) (by norm_num) hlo51 h51 (by norm_num)
        (by norm_num) hX hCv (hP51 hc hτ) (by norm_num)) w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  exact framePieceK16384_52 hn D hD c hτ hlo52 hθ1 hG hX hSS hSU hSD
      (covC_piece hn D c hτ (θl := 52/100) (θh := 528 / 1000) (lam1 := 591/1000) (by norm_num) hlo52 hθ1 (by norm_num)
        (by norm_num) hX hCv (hP52 hc hτ) (by norm_num)) w

end BstLean.Part188.Frame16384

open BstLean.Part188.Frame16384 in
#print axioms frameA_K_16384
