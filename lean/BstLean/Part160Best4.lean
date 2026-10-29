import BstLean.Part160Best3
import BstLean.Part160Split3
import BstLean.Part160ScLo
import BstLean.Part160Ledger4
import BstLean.Part160MFAll2

/-!
# Part 160 (file `Part160Best4`): the best frame constant and the least `n₀` of this part

Do not use `sorry`, `native_decide` or `axiom`. This file is generated from a template; the
rational constants were chosen outside Lean; Lean checks every inequality.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (eDir)
open BstLean.Part153 (XiS Xi4)
open BstLean.Part156

variable {n : ℕ}

/-- The piece `46/100 ≤ θ_in ≤ 47/100`: `N_cov = 1.157·1.067·0.47`, `ξ = 0.1304`,
`0.6802 ≤ e_b ≤ 0.7314`, `s = 5127 / 10000`, `sd = 203 / 500`. -/
lemma framePiece4_46 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (47 / 100) ≤
      1157 / 1000 * (107 / 100) * (47 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_46 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_46 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_46 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (47 / 100)) (a := 1157 / 1000 * (107 / 100) * (47 / 100))
    (eb := 3657 / 5000) (xi := 1304 / 10000) (e1 := 8553 / 10000) (e2 := 231 / 100000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (47 / 100)) / 24500) (sd := 203 / 500)
    (s := 5127 / 10000) (r := 3251 / 2500) (η := 23 / 100) (κ := 3729 / 1000) (ρ := 487 / 100000)
    (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 5703 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5127 / 10000 - 203 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (5127 / 10000 - 203 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48/100`: `N_cov = 1.157·1.067·0.48`, `ξ = 0.1337`,
`0.6753 ≤ e_b ≤ 0.7264`, `s = 5177 / 10000`, `sd = 41 / 100`. -/
lemma framePiece4_47 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 47 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (48 / 100) ≤
      1157 / 1000 * (107 / 100) * (48 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_47 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_47 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_47 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (48 / 100)) (a := 1157 / 1000 * (107 / 100) * (48 / 100))
    (eb := 454 / 625) (xi := 1337 / 10000) (e1 := 8523 / 10000) (e2 := 117 / 50000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (48 / 100)) / 24500) (sd := 41 / 100)
    (s := 5177 / 10000) (r := 13281 / 10000) (η := 23 / 100) (κ := 3811 / 1000) (ρ := 123 / 25000)
    (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 2873 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5177 / 10000 - 41 / 100) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (5177 / 10000 - 41 / 100) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49/100`: `N_cov = 1.157·1.067·0.49`, `ξ = 0.1371`,
`0.6705 ≤ e_b ≤ 0.7215`, `s = 2611 / 5000`, `sd = 413 / 1000`. -/
lemma framePiece4_48 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 48 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (49 / 100) ≤
      1157 / 1000 * (107 / 100) * (49 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_48 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_48 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_48 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (49 / 100)) (a := 1157 / 1000 * (107 / 100) * (49 / 100))
    (eb := 1443 / 2000) (xi := 1371 / 10000) (e1 := 1699 / 2000) (e2 := 237 / 100000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (49 / 100)) / 24500) (sd := 413 / 1000)
    (s := 2611 / 5000) (r := 13557 / 10000) (η := 23 / 100) (κ := 3893 / 1000) (ρ := 497 / 100000)
    (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 1447 / 2500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2611 / 5000 - 413 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (2611 / 5000 - 413 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50/100`: `N_cov = 1.157·1.067·0.5`, `ξ = 0.1405`,
`0.6657 ≤ e_b ≤ 0.7166`, `s = 5269 / 10000`, `sd = 417 / 1000`. -/
lemma framePiece4_49 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 49 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (50 / 100) ≤
      1157 / 1000 * (107 / 100) * (50 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_49 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_49 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_49 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (50 / 100)) (a := 1157 / 1000 * (107 / 100) * (50 / 100))
    (eb := 3583 / 5000) (xi := 1405 / 10000) (e1 := 4233 / 5000) (e2 := 3 / 1250)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (50 / 100)) / 24500) (sd := 417 / 1000)
    (s := 5269 / 10000) (r := 6917 / 5000) (η := 23 / 100) (κ := 497 / 125) (ρ := 251 / 50000)
    (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 5829 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5269 / 10000 - 417 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (5269 / 10000 - 417 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51/100`: `N_cov = 1.157·1.067·0.51`, `ξ = 0.1439`,
`0.661 ≤ e_b ≤ 0.7118`, `s = 1063 / 2000`, `sd = 421 / 1000`. -/
lemma framePiece4_50 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 50 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (51 / 100) ≤
      1157 / 1000 * (107 / 100) * (51 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_50 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_50 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_50 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (51 / 100)) (a := 1157 / 1000 * (107 / 100) * (51 / 100))
    (eb := 3559 / 5000) (xi := 1439 / 10000) (e1 := 8437 / 10000) (e2 := 243 / 100000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (51 / 100)) / 24500) (sd := 421 / 1000)
    (s := 1063 / 2000) (r := 14111 / 10000) (η := 23 / 100) (κ := 4059 / 1000) (ρ := 507 / 100000)
    (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 587 / 1000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1063 / 2000 - 421 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (1063 / 2000 - 421 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52/100`: `N_cov = 1.157·1.067·0.52`, `ξ = 0.1474`,
`0.6563 ≤ e_b ≤ 0.707`, `s = 5359 / 10000`, `sd = 53 / 125`. -/
lemma framePiece4_51 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 51 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (52 / 100) ≤
      1157 / 1000 * (107 / 100) * (52 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_51 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_51 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_51 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (52 / 100)) (a := 1157 / 1000 * (107 / 100) * (52 / 100))
    (eb := 707 / 1000) (xi := 1474 / 10000) (e1 := 8409 / 10000) (e2 := 123 / 50000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (52 / 100)) / 24500) (sd := 53 / 125)
    (s := 5359 / 10000) (r := 14387 / 10000) (η := 23 / 100) (κ := 2071 / 500) (ρ := 16 / 3125)
    (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 591 / 1000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5359 / 10000 - 53 / 125) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (5359 / 10000 - 53 / 125) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 53/100`: `N_cov = 1.157·1.067·0.53`, `ξ = 0.1509`,
`0.6517 ≤ e_b ≤ 0.7022`, `s = 5403 / 10000`, `sd = 427 / 1000`. -/
lemma framePiece4_52 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 52 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (53 / 100) ≤
      1157 / 1000 * (107 / 100) * (53 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_52 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_52 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_52 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (53 / 100)) (a := 1157 / 1000 * (107 / 100) * (53 / 100))
    (eb := 3511 / 5000) (xi := 1509 / 10000) (e1 := 419 / 500) (e2 := 249 / 100000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (53 / 100)) / 24500) (sd := 427 / 1000)
    (s := 5403 / 10000) (r := 1833 / 1250) (η := 23 / 100) (κ := 169 / 40) (ρ := 517 / 100000)
    (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 119 / 200)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5403 / 10000 - 427 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (5403 / 10000 - 427 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `53/100 ≤ θ_in ≤ 54/100`: `N_cov = 1.157·1.067·0.54`, `ξ = 0.1544`,
`0.647 ≤ e_b ≤ 0.6975`, `s = 2723 / 5000`, `sd = 431 / 1000`. -/
lemma framePiece4_53 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 53 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (54 / 100) ≤
      1157 / 1000 * (107 / 100) * (54 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_53 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_53 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_53 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (54 / 100)) (a := 1157 / 1000 * (107 / 100) * (54 / 100))
    (eb := 279 / 400) (xi := 1544 / 10000) (e1 := 522 / 625) (e2 := 63 / 25000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (54 / 100)) / 24500) (sd := 431 / 1000)
    (s := 2723 / 5000) (r := 14941 / 10000) (η := 23 / 100) (κ := 4309 / 1000) (ρ := 261 / 50000)
    (elo := 647 / 1000) (l1 := 8043 / 10000) (mu := 5989 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2723 / 5000 - 431 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (2723 / 5000 - 431 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `54/100 ≤ θ_in ≤ 55/100`: `N_cov = 1.157·1.067·0.55`, `ξ = 0.1579`,
`0.6425 ≤ e_b ≤ 0.6928`, `s = 5489 / 10000`, `sd = 217 / 500`. -/
lemma framePiece4_54 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 54 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      335 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (24500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (55 / 100) ≤
      1157 / 1000 * (107 / 100) * (55 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_54 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_54 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre22k_D_54 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 24500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (55 / 100)) (a := 1157 / 1000 * (107 / 100) * (55 / 100))
    (eb := 433 / 625) (xi := 1579 / 10000) (e1 := 2081 / 2500) (e2 := 127 / 50000)
    (N22 := 18334 / 1000 / 24500) (q := 2 * (1157 / 1000 * (1067 / 1000) * (55 / 100)) / 24500) (sd := 217 / 500)
    (s := 5489 / 10000) (r := 15217 / 10000) (η := 23 / 100) (κ := 549 / 125) (ρ := 527 / 100000)
    (elo := 257 / 400) (l1 := 1603 / 2000) (mu := 6027 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5489 / 10000 - 217 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 / (24500 ^ 3 * (5489 / 10000 - 217 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The Agent frame bound `(335 / 100)/n`, every `n ≥ 24500`**: the split of second order (with
the lower bound of the centre energy) on nine pieces of the window `0.46 ≤ θ_in ≤ 0.55`; on
`EA16 D` and the six events `SXi`, `SXi4n`, `SXi8n`, `SSc`, `SScU`, `SD'`. Constants on the
piece `[θ_lo, θ_hi]`: `N_cov = 1.157·1.067·θ_hi`, `ξ = the table `centre22k_D_k` (changes (A), (C), (D))`, `e_b` between the tables of
`Part160ScLo` and `Part160ScTab`. -/
theorem frameA4_24500 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXi n))
    (hE2 : E ⊆ agentEv D (SXi4n n))
    (hE3 : E ⊆ agentEv D (SXi8n n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n)) : FRAME_A_hyp D (335 / 100 / n) E := by
  intro c hc w
  obtain ⟨hτ, hlo46, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE1 hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE2 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE3 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hE4 hc hτ
  have hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hE5 hc hτ
  have hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n := hE6 hc hτ
  by_cases h46 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100
  · exact framePiece4_46 hn D hD c hτ hlo46 h46 hG hS hS4 hS8 hSS hSU hSD w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePiece4_47 hn D hD c hτ hlo47 h47 hG hS hS4 hS8 hSS hSU hSD w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePiece4_48 hn D hD c hτ hlo48 h48 hG hS hS4 hS8 hSS hSU hSD w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePiece4_49 hn D hD c hτ hlo49 h49 hG hS hS4 hS8 hSS hSU hSD w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePiece4_50 hn D hD c hτ hlo50 h50 hG hS hS4 hS8 hSS hSU hSD w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePiece4_51 hn D hD c hτ hlo51 h51 hG hS hS4 hS8 hSS hSU hSD w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  by_cases h52 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100
  · exact framePiece4_52 hn D hD c hτ hlo52 h52 hG hS hS4 hS8 hSS hSU hSD w
  have hlo53 : (53 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h52).le
  by_cases h53 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100
  · exact framePiece4_53 hn D hD c hτ hlo53 h53 hG hS hS4 hS8 hSS hSU hSD w
  have hlo54 : (54 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h53).le
  exact framePiece4_54 hn D hD c hτ hlo54 hθ1 hG hS hS4 hS8 hSS hSU hSD w

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 24500`.** For a design with the Agent centre of Part 154 (`AgentCentre154`; `paperDesign`
has it) and a `τ₀` that is a function of the World data (`TauWorld`): IF the events `H`, `E₁` of
the caller have charges with `δ_hid + v_W/h_W² + δ_extra + 34/100000 ≤ 0.0063`, and on
`H ∩ {H̄_W ≤ h_W} ∩ E₁` the World window (`τ₀ > 0`, `0.46 ≤ θ_in ≤ 0.55`), the World frame bound
`1.377/n` and the Agent replacement hold, THEN the program succeeds with probability at least
`99/100`. The Agent frame bound `(335 / 100)/n` is PROVED on seven Agent events of total charge at
most `34/100000`; the ledger is that of `classifier_frame_335`. -/
theorem classifier_agentframe4_24500 (hn : 24500 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 34 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hEv0 := events_with_EA16 hn16 D hτ hEv
  have hsub0 := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hEv1 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num)
    (SXi_charge hn16) hEv0
  have hsub1 := goodSet_inter_subset H (E₁ ∩ EA16 D)
    (agentEv D (SXi n)) (HbarW D) hWL
  have hEv2 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (SXi4n_charge hn16) hEv1
  have hsub2 := goodSet_inter_subset H ((E₁ ∩ EA16 D) ∩ agentEv D (SXi n))
    (agentEv D (SXi4n n)) (HbarW D) hWL
  have hEv3 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (SXi8n_charge hn16) hEv2
  have hsub3 := goodSet_inter_subset H (((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi4n n))
    (agentEv D (SXi8n n)) (HbarW D) hWL
  have hEv4 := events_with_agent D hτ (measurableSet_SSc n) (by norm_num)
    (SSc_charge_num hn16) hEv3
  have hsub4 := goodSet_inter_subset H ((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n))
    (agentEv D (SSc n)) (HbarW D) hWL
  have hEv5 := events_with_agent D hτ (measurableSet_SScU n) (by norm_num)
    (SScU_charge_num hn16) hEv4
  have hsub5 := goodSet_inter_subset H (((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n)) ∩ agentEv D (SSc n))
    (agentEv D (SScU n)) (HbarW D) hWL
  have hEv6 := events_with_agent D hτ (measurableSet_SD' n) (by norm_num)
    (fun c τ _ => SD'_charge (by omega) c τ) hEv5
  have hsub6 := goodSet_inter_subset H ((((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n)) ∩ agentEv D (SSc n)) ∩ agentEv D (SScU n))
    (agentEv D (SD' n)) (HbarW D) hWL
  have hsub : goodSet H (((((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n)) ∩ agentEv D (SSc n)) ∩ agentEv D (SScU n)) ∩ agentEv D (SD' n)) (HbarW D) hWL ⊆ goodSet H E₁ (HbarW D) hWL :=
    fun c hc => (hsub0 (hsub1 (hsub2 (hsub3 (hsub4 (hsub5 (hsub6 hc)))))))
  have hFA := frameA4_24500 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub1 (hsub2 (hsub3 (hsub4 (hsub5 (hsub6 hc)))))))
    (fun c hc => goodSet_inter_mem (hsub2 (hsub3 (hsub4 (hsub5 (hsub6 hc))))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 (hsub5 (hsub6 hc)))))
    (fun c hc => goodSet_inter_mem (hsub4 (hsub5 (hsub6 hc))))
    (fun c hc => goodSet_inter_mem (hsub5 (hsub6 hc)))
    (fun c hc => goodSet_inter_mem (hsub6 hc))
    (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_335 hn D t hEv6 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **The paper's design and the paper's charges, every `n ≥ 24500`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe4_24500 (hn : 24500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp (paperDesign n fT wT hf hw).toCentres H E₁
      (HbarW (paperDesign n fT wT hf hw)) δhidL vWL δextraL)
    (hWin : WINDOW_hyp (paperDesign n fT wT hf hw)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hFW : FRAME_W_hyp (paperDesign n fT wT hf hw).toCentres (cWL / n)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_agentframe4_24500 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv
    (by unfold δhidL vWL hWL δextraL; norm_num) hWin hFW hRA

/-- The piece `46/100 ≤ θ_in ≤ 47/100`: `N_cov = 1.157·1.067·0.47`, `ξ = 0.1653`,
`0.6802 ≤ e_b ≤ 0.7314`, `s = 1021 / 2000`, `sd = 393 / 1000`. -/
lemma framePiece4f_46 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (47 / 100) ≤
      1157 / 1000 * (107 / 100) * (47 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_46 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_46 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (47 / 100)) (a := 1157 / 1000 * (107 / 100) * (47 / 100))
    (eb := 3657 / 5000) (xi := 1653 / 10000) (e1 := 8553 / 10000) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (47 / 100)) / 16384) (sd := 393 / 1000)
    (s := 1021 / 2000) (r := 3251 / 2500) (η := 13 / 50) (κ := 1953 / 500) (ρ := 149 / 25000)
    (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 2861 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1021 / 2000 - 393 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (1021 / 2000 - 393 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48/100`: `N_cov = 1.157·1.067·0.48`, `ξ = 0.1653`,
`0.6753 ≤ e_b ≤ 0.7264`, `s = 1031 / 2000`, `sd = 397 / 1000`. -/
lemma framePiece4f_47 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 47 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (48 / 100) ≤
      1157 / 1000 * (107 / 100) * (48 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_47 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_47 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (48 / 100)) (a := 1157 / 1000 * (107 / 100) * (48 / 100))
    (eb := 454 / 625) (xi := 1653 / 10000) (e1 := 8523 / 10000) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (48 / 100)) / 16384) (sd := 397 / 1000)
    (s := 1031 / 2000) (r := 13281 / 10000) (η := 13 / 50) (κ := 3973 / 1000) (ρ := 301 / 50000)
    (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 1153 / 2000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1031 / 2000 - 397 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (1031 / 2000 - 397 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49/100`: `N_cov = 1.157·1.067·0.49`, `ξ = 0.1653`,
`0.6705 ≤ e_b ≤ 0.7215`, `s = 2601 / 5000`, `sd = 401 / 1000`. -/
lemma framePiece4f_48 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 48 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (49 / 100) ≤
      1157 / 1000 * (107 / 100) * (49 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_48 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_48 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (49 / 100)) (a := 1157 / 1000 * (107 / 100) * (49 / 100))
    (eb := 1443 / 2000) (xi := 1653 / 10000) (e1 := 1699 / 2000) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (49 / 100)) / 16384) (sd := 401 / 1000)
    (s := 2601 / 5000) (r := 13557 / 10000) (η := 1 / 4) (κ := 2019 / 500) (ρ := 19 / 3125)
    (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 2903 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2601 / 5000 - 401 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (2601 / 5000 - 401 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50/100`: `N_cov = 1.157·1.067·0.5`, `ξ = 0.1653`,
`0.6657 ≤ e_b ≤ 0.7166`, `s = 5249 / 10000`, `sd = 101 / 250`. -/
lemma framePiece4f_49 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 49 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (50 / 100) ≤
      1157 / 1000 * (107 / 100) * (50 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_49 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_49 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (50 / 100)) (a := 1157 / 1000 * (107 / 100) * (50 / 100))
    (eb := 3583 / 5000) (xi := 1653 / 10000) (e1 := 4233 / 5000) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (50 / 100)) / 16384) (sd := 101 / 250)
    (s := 5249 / 10000) (r := 6917 / 5000) (η := 1 / 4) (κ := 513 / 125) (ρ := 307 / 50000)
    (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 2923 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5249 / 10000 - 101 / 250) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (5249 / 10000 - 101 / 250) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51/100`: `N_cov = 1.157·1.067·0.51`, `ξ = 0.1653`,
`0.661 ≤ e_b ≤ 0.7118`, `s = 331 / 625`, `sd = 407 / 1000`. -/
lemma framePiece4f_50 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 50 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (51 / 100) ≤
      1157 / 1000 * (107 / 100) * (51 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_50 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_50 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (51 / 100)) (a := 1157 / 1000 * (107 / 100) * (51 / 100))
    (eb := 3559 / 5000) (xi := 1653 / 10000) (e1 := 8437 / 10000) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (51 / 100)) / 16384) (sd := 407 / 1000)
    (s := 331 / 625) (r := 14111 / 10000) (η := 1 / 4) (κ := 4169 / 1000) (ρ := 31 / 5000)
    (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 2943 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (331 / 625 - 407 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (331 / 625 - 407 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52/100`: `N_cov = 1.157·1.067·0.52`, `ξ = 0.1653`,
`0.6563 ≤ e_b ≤ 0.707`, `s = 267 / 500`, `sd = 411 / 1000`. -/
lemma framePiece4f_51 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 51 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (52 / 100) ≤
      1157 / 1000 * (107 / 100) * (52 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_51 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_51 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (52 / 100)) (a := 1157 / 1000 * (107 / 100) * (52 / 100))
    (eb := 707 / 1000) (xi := 1653 / 10000) (e1 := 8409 / 10000) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (52 / 100)) / 16384) (sd := 411 / 1000)
    (s := 267 / 500) (r := 14387 / 10000) (η := 1 / 4) (κ := 847 / 200) (ρ := 313 / 50000)
    (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 2963 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (267 / 500 - 411 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (267 / 500 - 411 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 53/100`: `N_cov = 1.157·1.067·0.53`, `ξ = 0.1653`,
`0.6517 ≤ e_b ≤ 0.7022`, `s = 2693 / 5000`, `sd = 207 / 500`. -/
lemma framePiece4f_52 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 52 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (53 / 100) ≤
      1157 / 1000 * (107 / 100) * (53 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_52 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_52 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (53 / 100)) (a := 1157 / 1000 * (107 / 100) * (53 / 100))
    (eb := 3511 / 5000) (xi := 1653 / 10000) (e1 := 419 / 500) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (53 / 100)) / 16384) (sd := 207 / 500)
    (s := 2693 / 5000) (r := 1833 / 1250) (η := 6 / 25) (κ := 43 / 10) (ρ := 79 / 12500)
    (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 1193 / 2000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2693 / 5000 - 207 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (2693 / 5000 - 207 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `53/100 ≤ θ_in ≤ 54/100`: `N_cov = 1.157·1.067·0.54`, `ξ = 0.1653`,
`0.647 ≤ e_b ≤ 0.6975`, `s = 5429 / 10000`, `sd = 417 / 1000`. -/
lemma framePiece4f_53 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 53 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (54 / 100) ≤
      1157 / 1000 * (107 / 100) * (54 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_53 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_53 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (54 / 100)) (a := 1157 / 1000 * (107 / 100) * (54 / 100))
    (eb := 279 / 400) (xi := 1653 / 10000) (e1 := 522 / 625) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (54 / 100)) / 16384) (sd := 417 / 1000)
    (s := 5429 / 10000) (r := 14941 / 10000) (η := 6 / 25) (κ := 873 / 200) (ρ := 319 / 50000)
    (elo := 647 / 1000) (l1 := 8043 / 10000) (mu := 1501 / 2500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5429 / 10000 - 417 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (5429 / 10000 - 417 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `54/100 ≤ θ_in ≤ 55/100`: `N_cov = 1.157·1.067·0.55`, `ξ = 0.1653`,
`0.6425 ≤ e_b ≤ 0.6928`, `s = 342 / 625`, `sd = 21 / 50`. -/
lemma framePiece4f_54 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 54 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n)
    (hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      36 / 10 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (55 / 100) ≤
      1157 / 1000 * (107 / 100) * (55 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_54 hn16 hτ hθ0 hθ1' hG hSS
  have hlo := eb16_lower_54 hn16 hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hSU
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_D hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (55 / 100)) (a := 1157 / 1000 * (107 / 100) * (55 / 100))
    (eb := 433 / 625) (xi := 1653 / 10000) (e1 := 2081 / 2500) (e2 := 159 / 50000)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (55 / 100)) / 16384) (sd := 21 / 50)
    (s := 342 / 625) (r := 15217 / 10000) (η := 6 / 25) (κ := 443 / 100) (ρ := 161 / 25000)
    (elo := 257 / 400) (l1 := 1603 / 2000) (mu := 6041 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (342 / 625 - 21 / 50) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (342 / 625 - 21 / 50) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The Agent frame bound `(36 / 10)/n`, every `n ≥ 16384`**: the split of second order (with
the lower bound of the centre energy) on nine pieces of the window `0.46 ≤ θ_in ≤ 0.55`; on
`EA16 D` and the six events `SXi`, `SXi4n`, `SXi8n`, `SSc`, `SScU`, `SD'`. Constants on the
piece `[θ_lo, θ_hi]`: `N_cov = 1.157·1.067·θ_hi`, `ξ = 0.1653 (`centre16_D`)`, `e_b` between the tables of
`Part160ScLo` and `Part160ScTab`. -/
theorem frameA4f_16384 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXi n))
    (hE2 : E ⊆ agentEv D (SXi4n n))
    (hE3 : E ⊆ agentEv D (SXi8n n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n)) : FRAME_A_hyp D (36 / 10 / n) E := by
  intro c hc w
  obtain ⟨hτ, hlo46, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE1 hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE2 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE3 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hE4 hc hτ
  have hSU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hE5 hc hτ
  have hSD : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SD' n := hE6 hc hτ
  by_cases h46 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100
  · exact framePiece4f_46 hn D hD c hτ hlo46 h46 hG hS hS4 hS8 hSS hSU hSD w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePiece4f_47 hn D hD c hτ hlo47 h47 hG hS hS4 hS8 hSS hSU hSD w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePiece4f_48 hn D hD c hτ hlo48 h48 hG hS hS4 hS8 hSS hSU hSD w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePiece4f_49 hn D hD c hτ hlo49 h49 hG hS hS4 hS8 hSS hSU hSD w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePiece4f_50 hn D hD c hτ hlo50 h50 hG hS hS4 hS8 hSS hSU hSD w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePiece4f_51 hn D hD c hτ hlo51 h51 hG hS hS4 hS8 hSS hSU hSD w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  by_cases h52 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100
  · exact framePiece4f_52 hn D hD c hτ hlo52 h52 hG hS hS4 hS8 hSS hSU hSD w
  have hlo53 : (53 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h52).le
  by_cases h53 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100
  · exact framePiece4f_53 hn D hD c hτ hlo53 h53 hG hS hS4 hS8 hSS hSU hSD w
  have hlo54 : (54 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h53).le
  exact framePiece4f_54 hn D hD c hτ hlo54 hθ1 hG hS hS4 hS8 hSS hSU hSD w


end BstLean.Part160

open BstLean.Part160 in
#print axioms frameA4_24500
open BstLean.Part160 in
#print axioms classifier_agentframe4_24500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe4_24500
open BstLean.Part160 in
#print axioms frameA4f_16384
