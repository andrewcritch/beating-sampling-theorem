import BstLean.Part160Best3
import BstLean.Part160Split3
import BstLean.Part160ScLo
import BstLean.Part160Ledger4
import BstLean.Part160Ledger5
import BstLean.Part160MFAll2

/-!
# Part 160 (file `Part160Best5`): the best frame constant and the least `n₀` of this part

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

/-- The piece `46/100 ≤ θ_in ≤ 47/100`: `N_cov = 1.157·1.067·0.47`, `ξ = 0.0803`,
`0.6802 ≤ e_b ≤ 0.7314`, `s = 2567 / 5000`, `sd = 101 / 250`. -/
lemma framePiece5_46 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_46 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (47 / 100)) (a := 1157 / 1000 * (107 / 100) * (47 / 100))
    (eb := 3657 / 5000) (xi := 803 / 10000) (e1 := 8553 / 10000) (e2 := 187 / 100000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (47 / 100)) / 23000) (sd := 101 / 250)
    (s := 2567 / 5000) (r := 3251 / 2500) (η := 9 / 50) (κ := 687 / 200) (ρ := 503 / 100000)
    (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 5697 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2567 / 5000 - 101 / 250) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (2567 / 5000 - 101 / 250) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48/100`: `N_cov = 1.157·1.067·0.48`, `ξ = 0.0815`,
`0.6753 ≤ e_b ≤ 0.7264`, `s = 5183 / 10000`, `sd = 51 / 125`. -/
lemma framePiece5_47 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_47 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (48 / 100)) (a := 1157 / 1000 * (107 / 100) * (48 / 100))
    (eb := 454 / 625) (xi := 815 / 10000) (e1 := 8523 / 10000) (e2 := 189 / 100000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (48 / 100)) / 23000) (sd := 51 / 125)
    (s := 5183 / 10000) (r := 13281 / 10000) (η := 9 / 50) (κ := 438 / 125) (ρ := 127 / 25000)
    (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 5741 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5183 / 10000 - 51 / 125) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (5183 / 10000 - 51 / 125) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49/100`: `N_cov = 1.157·1.067·0.49`, `ξ = 0.0827`,
`0.6705 ≤ e_b ≤ 0.7215`, `s = 5229 / 10000`, `sd = 411 / 1000`. -/
lemma framePiece5_48 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_48 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (49 / 100)) (a := 1157 / 1000 * (107 / 100) * (49 / 100))
    (eb := 1443 / 2000) (xi := 827 / 10000) (e1 := 1699 / 2000) (e2 := 19 / 10000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (49 / 100)) / 23000) (sd := 411 / 1000)
    (s := 5229 / 10000) (r := 13557 / 10000) (η := 9 / 50) (κ := 1787 / 500) (ρ := 513 / 100000)
    (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 2891 / 5000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5229 / 10000 - 411 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (5229 / 10000 - 411 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50/100`: `N_cov = 1.157·1.067·0.5`, `ξ = 0.0839`,
`0.6657 ≤ e_b ≤ 0.7166`, `s = 1319 / 2500`, `sd = 83 / 200`. -/
lemma framePiece5_49 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_49 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (50 / 100)) (a := 1157 / 1000 * (107 / 100) * (50 / 100))
    (eb := 3583 / 5000) (xi := 839 / 10000) (e1 := 4233 / 5000) (e2 := 191 / 100000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (50 / 100)) / 23000) (sd := 83 / 200)
    (s := 1319 / 2500) (r := 6917 / 5000) (η := 9 / 50) (κ := 911 / 250) (ρ := 519 / 100000)
    (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 5823 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1319 / 2500 - 83 / 200) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (1319 / 2500 - 83 / 200) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51/100`: `N_cov = 1.157·1.067·0.51`, `ξ = 0.0851`,
`0.661 ≤ e_b ≤ 0.7118`, `s = 2661 / 5000`, `sd = 209 / 500`. -/
lemma framePiece5_50 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_50 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (51 / 100)) (a := 1157 / 1000 * (107 / 100) * (51 / 100))
    (eb := 3559 / 5000) (xi := 851 / 10000) (e1 := 8437 / 10000) (e2 := 193 / 100000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (51 / 100)) / 23000) (sd := 209 / 500)
    (s := 2661 / 5000) (r := 14111 / 10000) (η := 9 / 50) (κ := 1857 / 500) (ρ := 131 / 25000)
    (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 733 / 1250)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2661 / 5000 - 209 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (2661 / 5000 - 209 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52/100`: `N_cov = 1.157·1.067·0.52`, `ξ = 0.0862`,
`0.6563 ≤ e_b ≤ 0.707`, `s = 2683 / 5000`, `sd = 211 / 500`. -/
lemma framePiece5_51 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_51 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (52 / 100)) (a := 1157 / 1000 * (107 / 100) * (52 / 100))
    (eb := 707 / 1000) (xi := 862 / 10000) (e1 := 8409 / 10000) (e2 := 97 / 50000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (52 / 100)) / 23000) (sd := 211 / 500)
    (s := 2683 / 5000) (r := 14387 / 10000) (η := 9 / 50) (κ := 3783 / 1000) (ρ := 529 / 100000)
    (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 369 / 625)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2683 / 5000 - 211 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (2683 / 5000 - 211 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 53/100`: `N_cov = 1.157·1.067·0.53`, `ξ = 0.0874`,
`0.6517 ≤ e_b ≤ 0.7022`, `s = 5411 / 10000`, `sd = 17 / 40`. -/
lemma framePiece5_52 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_52 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (53 / 100)) (a := 1157 / 1000 * (107 / 100) * (53 / 100))
    (eb := 3511 / 5000) (xi := 874 / 10000) (e1 := 419 / 500) (e2 := 39 / 20000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (53 / 100)) / 23000) (sd := 17 / 40)
    (s := 5411 / 10000) (r := 1833 / 1250) (η := 9 / 50) (κ := 963 / 250) (ρ := 267 / 50000)
    (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 5943 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5411 / 10000 - 17 / 40) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (5411 / 10000 - 17 / 40) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `53/100 ≤ θ_in ≤ 54/100`: `N_cov = 1.157·1.067·0.54`, `ξ = 0.0885`,
`0.647 ≤ e_b ≤ 0.6975`, `s = 2727 / 5000`, `sd = 429 / 1000`. -/
lemma framePiece5_53 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_53 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (54 / 100)) (a := 1157 / 1000 * (107 / 100) * (54 / 100))
    (eb := 279 / 400) (xi := 885 / 10000) (e1 := 522 / 625) (e2 := 197 / 100000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (54 / 100)) / 23000) (sd := 429 / 1000)
    (s := 2727 / 5000) (r := 14941 / 10000) (η := 9 / 50) (κ := 1961 / 500) (ρ := 539 / 100000)
    (elo := 647 / 1000) (l1 := 8043 / 10000) (mu := 5983 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2727 / 5000 - 429 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (2727 / 5000 - 429 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `54/100 ≤ θ_in ≤ 55/100`: `N_cov = 1.157·1.067·0.55`, `ξ = 0.0895`,
`0.6425 ≤ e_b ≤ 0.6928`, `s = 687 / 1250`, `sd = 54 / 125`. -/
lemma framePiece5_54 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      305 / 100 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (23000 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre22k_54 (by omega) hτ hθ0 hθ1 hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 23000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (55 / 100)) (a := 1157 / 1000 * (107 / 100) * (55 / 100))
    (eb := 433 / 625) (xi := 895 / 10000) (e1 := 2081 / 2500) (e2 := 99 / 50000)
    (N22 := 18334 / 1000 / 23000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (55 / 100)) / 23000) (sd := 54 / 125)
    (s := 687 / 1250) (r := 15217 / 10000) (η := 9 / 50) (κ := 399 / 100) (ρ := 17 / 3125)
    (elo := 257 / 400) (l1 := 1603 / 2000) (mu := 301 / 500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (687 / 1250 - 54 / 125) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 / (23000 ^ 3 * (687 / 1250 - 54 / 125) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The Agent frame bound `(305 / 100)/n`, every `n ≥ 23000`**: the split of second order (with
the lower bound of the centre energy) on nine pieces of the window `0.46 ≤ θ_in ≤ 0.55`; on
`EA16 D` and the six events `SXi`, `SXi4n`, `SXi8n`, `SSc`, `SScU`, `SD'`. Constants on the
piece `[θ_lo, θ_hi]`: `N_cov = 1.157·1.067·θ_hi`, `ξ = the table `centre22k_k` (changes (A), (B), (C), (D))`, `e_b` between the tables of
`Part160ScLo` and `Part160ScTab`. -/
theorem frameA5_23000 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXi n))
    (hE2 : E ⊆ agentEv D (SXi4n n))
    (hE3 : E ⊆ agentEv D (SXi8n n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n)) : FRAME_A_hyp D (305 / 100 / n) E := by
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
  · exact framePiece5_46 hn D hD c hτ hlo46 h46 hG hS hS4 hS8 hSS hSU hSD w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePiece5_47 hn D hD c hτ hlo47 h47 hG hS hS4 hS8 hSS hSU hSD w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePiece5_48 hn D hD c hτ hlo48 h48 hG hS hS4 hS8 hSS hSU hSD w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePiece5_49 hn D hD c hτ hlo49 h49 hG hS hS4 hS8 hSS hSU hSD w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePiece5_50 hn D hD c hτ hlo50 h50 hG hS hS4 hS8 hSS hSU hSD w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePiece5_51 hn D hD c hτ hlo51 h51 hG hS hS4 hS8 hSS hSU hSD w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  by_cases h52 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100
  · exact framePiece5_52 hn D hD c hτ hlo52 h52 hG hS hS4 hS8 hSS hSU hSD w
  have hlo53 : (53 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h52).le
  by_cases h53 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100
  · exact framePiece5_53 hn D hD c hτ hlo53 h53 hG hS hS4 hS8 hSS hSU hSD w
  have hlo54 : (54 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h53).le
  exact framePiece5_54 hn D hD c hτ hlo54 hθ1 hG hS hS4 hS8 hSS hSU hSD w

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 23000`.** For a design with the Agent centre of Part 154 (`AgentCentre154`; `paperDesign`
has it) and a `τ₀` that is a function of the World data (`TauWorld`): IF the events `H`, `E₁` of
the caller have charges with `δ_hid + v_W/h_W² + δ_extra + 34/100000 ≤ 0.0063`, and on
`H ∩ {H̄_W ≤ h_W} ∩ E₁` the World window (`τ₀ > 0`, `0.46 ≤ θ_in ≤ 0.55`), the World frame bound
`1.377/n` and the Agent replacement hold, THEN the program succeeds with probability at least
`99/100`. The Agent frame bound `(305 / 100)/n` is PROVED on seven Agent events of total charge at
most `34/100000`; the ledger is that of `classifier_frame_305`. -/
theorem classifier_agentframe5_23000 (hn : 23000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
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
  have hFA := frameA5_23000 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub1 (hsub2 (hsub3 (hsub4 (hsub5 (hsub6 hc)))))))
    (fun c hc => goodSet_inter_mem (hsub2 (hsub3 (hsub4 (hsub5 (hsub6 hc))))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 (hsub5 (hsub6 hc)))))
    (fun c hc => goodSet_inter_mem (hsub4 (hsub5 (hsub6 hc))))
    (fun c hc => goodSet_inter_mem (hsub5 (hsub6 hc)))
    (fun c hc => goodSet_inter_mem (hsub6 hc))
    (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_305 hn D t hEv6 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **The paper's design and the paper's charges, every `n ≥ 23000`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe5_23000 (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
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
  classifier_agentframe5_23000 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv
    (by unfold δhidL vWL hWL δextraL; norm_num) hWin hFW hRA

/-- The piece `46/100 ≤ θ_in ≤ 47/100`: `N_cov = 1.157·1.067·0.47`, `ξ = 0.1022`,
`0.6802 ≤ e_b ≤ 0.7314`, `s = 5117 / 10000`, `sd = 393 / 1000`. -/
lemma framePiece5f_46 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (47 / 100)) (a := 1157 / 1000 * (107 / 100) * (47 / 100))
    (eb := 3657 / 5000) (xi := 1022 / 10000) (e1 := 8553 / 10000) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (47 / 100)) / 16384) (sd := 393 / 1000)
    (s := 5117 / 10000) (r := 3251 / 2500) (η := 1 / 5) (κ := 3571 / 1000) (ρ := 149 / 25000)
    (elo := 3401 / 5000) (l1 := 8247 / 10000) (mu := 357 / 625)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5117 / 10000 - 393 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (5117 / 10000 - 393 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48/100`: `N_cov = 1.157·1.067·0.48`, `ξ = 0.1022`,
`0.6753 ≤ e_b ≤ 0.7264`, `s = 5167 / 10000`, `sd = 397 / 1000`. -/
lemma framePiece5f_47 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (48 / 100)) (a := 1157 / 1000 * (107 / 100) * (48 / 100))
    (eb := 454 / 625) (xi := 1022 / 10000) (e1 := 8523 / 10000) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (48 / 100)) / 16384) (sd := 397 / 1000)
    (s := 5167 / 10000) (r := 13281 / 10000) (η := 1 / 5) (κ := 1817 / 500) (ρ := 301 / 50000)
    (elo := 6753 / 10000) (l1 := 8217 / 10000) (mu := 1151 / 2000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5167 / 10000 - 397 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (5167 / 10000 - 397 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49/100`: `N_cov = 1.157·1.067·0.49`, `ξ = 0.1022`,
`0.6705 ≤ e_b ≤ 0.7215`, `s = 5213 / 10000`, `sd = 2 / 5`. -/
lemma framePiece5f_48 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (49 / 100)) (a := 1157 / 1000 * (107 / 100) * (49 / 100))
    (eb := 1443 / 2000) (xi := 1022 / 10000) (e1 := 1699 / 2000) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (49 / 100)) / 16384) (sd := 2 / 5)
    (s := 5213 / 10000) (r := 13557 / 10000) (η := 1 / 5) (κ := 462 / 125) (ρ := 19 / 3125)
    (elo := 1341 / 2000) (l1 := 2047 / 2500) (mu := 1449 / 2500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5213 / 10000 - 2 / 5) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (5213 / 10000 - 2 / 5) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50/100`: `N_cov = 1.157·1.067·0.5`, `ξ = 0.1022`,
`0.6657 ≤ e_b ≤ 0.7166`, `s = 263 / 500`, `sd = 101 / 250`. -/
lemma framePiece5f_49 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (50 / 100)) (a := 1157 / 1000 * (107 / 100) * (50 / 100))
    (eb := 3583 / 5000) (xi := 1022 / 10000) (e1 := 4233 / 5000) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (50 / 100)) / 16384) (sd := 101 / 250)
    (s := 263 / 500) (r := 6917 / 5000) (η := 1 / 5) (κ := 94 / 25) (ρ := 307 / 50000)
    (elo := 6657 / 10000) (l1 := 8159 / 10000) (mu := 5837 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (263 / 500 - 101 / 250) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (263 / 500 - 101 / 250) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51/100`: `N_cov = 1.157·1.067·0.51`, `ξ = 0.1022`,
`0.661 ≤ e_b ≤ 0.7118`, `s = 2653 / 5000`, `sd = 407 / 1000`. -/
lemma framePiece5f_50 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (51 / 100)) (a := 1157 / 1000 * (107 / 100) * (51 / 100))
    (eb := 3559 / 5000) (xi := 1022 / 10000) (e1 := 8437 / 10000) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (51 / 100)) / 16384) (sd := 407 / 1000)
    (s := 2653 / 5000) (r := 14111 / 10000) (η := 1 / 5) (κ := 3823 / 1000) (ρ := 31 / 5000)
    (elo := 661 / 1000) (l1 := 813 / 1000) (mu := 5877 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2653 / 5000 - 407 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (2653 / 5000 - 407 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52/100`: `N_cov = 1.157·1.067·0.52`, `ξ = 0.1022`,
`0.6563 ≤ e_b ≤ 0.707`, `s = 5351 / 10000`, `sd = 411 / 1000`. -/
lemma framePiece5f_51 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (52 / 100)) (a := 1157 / 1000 * (107 / 100) * (52 / 100))
    (eb := 707 / 1000) (xi := 1022 / 10000) (e1 := 8409 / 10000) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (52 / 100)) / 16384) (sd := 411 / 1000)
    (s := 5351 / 10000) (r := 14387 / 10000) (η := 19 / 100) (κ := 777 / 200) (ρ := 313 / 50000)
    (elo := 6563 / 10000) (l1 := 8101 / 10000) (mu := 5917 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5351 / 10000 - 411 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (5351 / 10000 - 411 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 53/100`: `N_cov = 1.157·1.067·0.53`, `ξ = 0.1022`,
`0.6517 ≤ e_b ≤ 0.7022`, `s = 1349 / 2500`, `sd = 207 / 500`. -/
lemma framePiece5f_52 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (53 / 100)) (a := 1157 / 1000 * (107 / 100) * (53 / 100))
    (eb := 3511 / 5000) (xi := 1022 / 10000) (e1 := 419 / 500) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (53 / 100)) / 16384) (sd := 207 / 500)
    (s := 1349 / 2500) (r := 1833 / 1250) (η := 19 / 100) (κ := 3947 / 1000) (ρ := 79 / 12500)
    (elo := 6517 / 10000) (l1 := 1009 / 1250) (mu := 1489 / 2500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1349 / 2500 - 207 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (1349 / 2500 - 207 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `53/100 ≤ θ_in ≤ 54/100`: `N_cov = 1.157·1.067·0.54`, `ξ = 0.1022`,
`0.647 ≤ e_b ≤ 0.6975`, `s = 68 / 125`, `sd = 417 / 1000`. -/
lemma framePiece5f_53 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (54 / 100)) (a := 1157 / 1000 * (107 / 100) * (54 / 100))
    (eb := 279 / 400) (xi := 1022 / 10000) (e1 := 522 / 625) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (54 / 100)) / 16384) (sd := 417 / 1000)
    (s := 68 / 125) (r := 14941 / 10000) (η := 19 / 100) (κ := 401 / 100) (ρ := 319 / 50000)
    (elo := 647 / 1000) (l1 := 8043 / 10000) (mu := 1199 / 2000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (68 / 125 - 417 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (68 / 125 - 417 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `54/100 ≤ θ_in ≤ 55/100`: `N_cov = 1.157·1.067·0.55`, `ξ = 0.1022`,
`0.6425 ≤ e_b ≤ 0.6928`, `s = 2741 / 5000`, `sd = 21 / 50`. -/
lemma framePiece5f_54 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
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
      33 / 10 / n * ∑ j, w j ^ 2 := by
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
  have c1 := centre16_BD hn16 hτ hθ0' hθ1' hG hSD
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point3 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (55 / 100)) (a := 1157 / 1000 * (107 / 100) * (55 / 100))
    (eb := 433 / 625) (xi := 1022 / 10000) (e1 := 2081 / 2500) (e2 := 1 / 400)
    (N22 := 18334 / 1000 / 16384) (q := 2 * (1157 / 1000 * (1067 / 1000) * (55 / 100)) / 16384) (sd := 21 / 50)
    (s := 2741 / 5000) (r := 15217 / 10000) (η := 19 / 100) (κ := 509 / 125) (ρ := 161 / 25000)
    (elo := 257 / 400) (l1 := 1603 / 2000) (mu := 377 / 625)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    hlo (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2741 / 5000 - 21 / 50) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 / (16384 ^ 3 * (2741 / 5000 - 21 / 50) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The Agent frame bound `(33 / 10)/n`, every `n ≥ 16384`**: the split of second order (with
the lower bound of the centre energy) on nine pieces of the window `0.46 ≤ θ_in ≤ 0.55`; on
`EA16 D` and the six events `SXi`, `SXi4n`, `SXi8n`, `SSc`, `SScU`, `SD'`. Constants on the
piece `[θ_lo, θ_hi]`: `N_cov = 1.157·1.067·θ_hi`, `ξ = 0.1022 (`centre16_BD`)`, `e_b` between the tables of
`Part160ScLo` and `Part160ScTab`. -/
theorem frameA5f_16384 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D)
    (hE1 : E ⊆ agentEv D (SXi n))
    (hE2 : E ⊆ agentEv D (SXi4n n))
    (hE3 : E ⊆ agentEv D (SXi8n n))
    (hE4 : E ⊆ agentEv D (SSc n))
    (hE5 : E ⊆ agentEv D (SScU n))
    (hE6 : E ⊆ agentEv D (SD' n)) : FRAME_A_hyp D (33 / 10 / n) E := by
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
  · exact framePiece5f_46 hn D hD c hτ hlo46 h46 hG hS hS4 hS8 hSS hSU hSD w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePiece5f_47 hn D hD c hτ hlo47 h47 hG hS hS4 hS8 hSS hSU hSD w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePiece5f_48 hn D hD c hτ hlo48 h48 hG hS hS4 hS8 hSS hSU hSD w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePiece5f_49 hn D hD c hτ hlo49 h49 hG hS hS4 hS8 hSS hSU hSD w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePiece5f_50 hn D hD c hτ hlo50 h50 hG hS hS4 hS8 hSS hSU hSD w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePiece5f_51 hn D hD c hτ hlo51 h51 hG hS hS4 hS8 hSS hSU hSD w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  by_cases h52 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100
  · exact framePiece5f_52 hn D hD c hτ hlo52 h52 hG hS hS4 hS8 hSS hSU hSD w
  have hlo53 : (53 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h52).le
  by_cases h53 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100
  · exact framePiece5f_53 hn D hD c hτ hlo53 h53 hG hS hS4 hS8 hSS hSU hSD w
  have hlo54 : (54 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h53).le
  exact framePiece5f_54 hn D hD c hτ hlo54 hθ1 hG hS hS4 hS8 hSS hSU hSD w


end BstLean.Part160

open BstLean.Part160 in
#print axioms frameA5_23000
open BstLean.Part160 in
#print axioms classifier_agentframe5_23000
open BstLean.Part160 in
#print axioms classifier_paper_agentframe5_23000
open BstLean.Part160 in
#print axioms frameA5f_16384
