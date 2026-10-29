import BstLean.Part160Best2
import BstLean.Part160Theta
import BstLean.Part160ScTab

/-!
# Part 160 (file `Part160Best3`): the frame constant on pieces of the window of `θ_in`

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

/-- `x ≤ y` gives `x·γ_A/n ≤ y·γ_A/n`. -/
lemma gn_mono {x y : ℝ} (h : x ≤ y) : x * (2 / (n : ℝ)) / n ≤ y * (2 / (n : ℝ)) / n := by
  have : (0 : ℝ) ≤ 2 / (n : ℝ) / n := by positivity
  have e1 : x * (2 / (n : ℝ)) / n = x * (2 / (n : ℝ) / n) := by ring
  have e2 : y * (2 / (n : ℝ)) / n = y * (2 / (n : ℝ) / n) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right h this


/-- The piece `46/100 ≤ θ_in ≤ 47/100`: `N_cov = 1.157·1.067·0.47`, `e_b ≤ 0.7314`,
`s = 5121 / 10000`, `sd = 52 / 125`. -/
lemma framePiece_46 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (47 / 100) ≤
      1157 / 1000 * (107 / 100) * (47 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_46 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (47 / 100)) (a := 1157 / 1000 * (107 / 100) * (47 / 100))
    (eb := 3657 / 5000) (xi := 221 / 1000) (e1 := 8553 / 10000) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (47 / 100)) / 28000) (sd := 52 / 125)
    (s := 5121 / 10000) (r := 3251 / 2500) (η := 3 / 10) (κ := 2081 / 500) (ρ := 57 / 12500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5121 / 10000 - 52 / 125) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (47 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (5121 / 10000 - 52 / 125) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `47/100 ≤ θ_in ≤ 48/100`: `N_cov = 1.157·1.067·0.48`, `e_b ≤ 0.7264`,
`s = 5171 / 10000`, `sd = 21 / 50`. -/
lemma framePiece_47 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 47 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (48 / 100) ≤
      1157 / 1000 * (107 / 100) * (48 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_47 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (48 / 100)) (a := 1157 / 1000 * (107 / 100) * (48 / 100))
    (eb := 454 / 625) (xi := 221 / 1000) (e1 := 8523 / 10000) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (48 / 100)) / 28000) (sd := 21 / 50)
    (s := 5171 / 10000) (r := 13281 / 10000) (η := 3 / 10) (κ := 423 / 100) (ρ := 461 / 100000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5171 / 10000 - 21 / 50) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (48 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (5171 / 10000 - 21 / 50) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `48/100 ≤ θ_in ≤ 49/100`: `N_cov = 1.157·1.067·0.49`, `e_b ≤ 0.7215`,
`s = 5217 / 10000`, `sd = 423 / 1000`. -/
lemma framePiece_48 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 48 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (49 / 100) ≤
      1157 / 1000 * (107 / 100) * (49 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_48 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (49 / 100)) (a := 1157 / 1000 * (107 / 100) * (49 / 100))
    (eb := 1443 / 2000) (xi := 221 / 1000) (e1 := 1699 / 2000) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (49 / 100)) / 28000) (sd := 423 / 1000)
    (s := 5217 / 10000) (r := 13557 / 10000) (η := 29 / 100) (κ := 2149 / 500) (ρ := 93 / 20000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (5217 / 10000 - 423 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (49 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (5217 / 10000 - 423 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `49/100 ≤ θ_in ≤ 50/100`: `N_cov = 1.157·1.067·0.5`, `e_b ≤ 0.7166`,
`s = 329 / 625`, `sd = 427 / 1000`. -/
lemma framePiece_49 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 49 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (50 / 100) ≤
      1157 / 1000 * (107 / 100) * (50 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_49 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (50 / 100)) (a := 1157 / 1000 * (107 / 100) * (50 / 100))
    (eb := 3583 / 5000) (xi := 221 / 1000) (e1 := 4233 / 5000) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (50 / 100)) / 28000) (sd := 427 / 1000)
    (s := 329 / 625) (r := 6917 / 5000) (η := 29 / 100) (κ := 873 / 200) (ρ := 47 / 10000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (329 / 625 - 427 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (50 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (329 / 625 - 427 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `50/100 ≤ θ_in ≤ 51/100`: `N_cov = 1.157·1.067·0.51`, `e_b ≤ 0.7118`,
`s = 531 / 1000`, `sd = 431 / 1000`. -/
lemma framePiece_50 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 50 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (51 / 100) ≤
      1157 / 1000 * (107 / 100) * (51 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_50 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (51 / 100)) (a := 1157 / 1000 * (107 / 100) * (51 / 100))
    (eb := 3559 / 5000) (xi := 221 / 1000) (e1 := 8437 / 10000) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (51 / 100)) / 28000) (sd := 431 / 1000)
    (s := 531 / 1000) (r := 14111 / 10000) (η := 29 / 100) (κ := 4433 / 1000) (ρ := 19 / 4000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (531 / 1000 - 431 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (51 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (531 / 1000 - 431 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `51/100 ≤ θ_in ≤ 52/100`: `N_cov = 1.157·1.067·0.52`, `e_b ≤ 0.707`,
`s = 1071 / 2000`, `sd = 217 / 500`. -/
lemma framePiece_51 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 51 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (52 / 100) ≤
      1157 / 1000 * (107 / 100) * (52 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_51 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (52 / 100)) (a := 1157 / 1000 * (107 / 100) * (52 / 100))
    (eb := 707 / 1000) (xi := 221 / 1000) (e1 := 8409 / 10000) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (52 / 100)) / 28000) (sd := 217 / 500)
    (s := 1071 / 2000) (r := 14387 / 10000) (η := 7 / 25) (κ := 4501 / 1000) (ρ := 479 / 100000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1071 / 2000 - 217 / 500) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (52 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (1071 / 2000 - 217 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `52/100 ≤ θ_in ≤ 53/100`: `N_cov = 1.157·1.067·0.53`, `e_b ≤ 0.7022`,
`s = 27 / 50`, `sd = 437 / 1000`. -/
lemma framePiece_52 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 52 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (53 / 100) ≤
      1157 / 1000 * (107 / 100) * (53 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_52 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (53 / 100)) (a := 1157 / 1000 * (107 / 100) * (53 / 100))
    (eb := 3511 / 5000) (xi := 221 / 1000) (e1 := 419 / 500) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (53 / 100)) / 28000) (sd := 437 / 1000)
    (s := 27 / 50) (r := 1833 / 1250) (η := 7 / 25) (κ := 571 / 125) (ρ := 121 / 25000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (27 / 50 - 437 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (53 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (27 / 50 - 437 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `53/100 ≤ θ_in ≤ 54/100`: `N_cov = 1.157·1.067·0.54`, `e_b ≤ 0.6975`,
`s = 1361 / 2500`, `sd = 441 / 1000`. -/
lemma framePiece_53 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 53 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (54 / 100) ≤
      1157 / 1000 * (107 / 100) * (54 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_53 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (54 / 100)) (a := 1157 / 1000 * (107 / 100) * (54 / 100))
    (eb := 279 / 400) (xi := 221 / 1000) (e1 := 522 / 625) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (54 / 100)) / 28000) (sd := 441 / 1000)
    (s := 1361 / 2500) (r := 14941 / 10000) (η := 7 / 25) (κ := 927 / 200) (ρ := 61 / 12500)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1361 / 2500 - 441 / 1000) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (54 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (1361 / 2500 - 441 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- The piece `54/100 ≤ θ_in ≤ 55/100`: `N_cov = 1.157·1.067·0.55`, `e_b ≤ 0.6928`,
`s = 2743 / 5000`, `sd = 111 / 250`. -/
lemma framePiece_54 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 54 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n)
    (hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n)
    (hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n)
    (hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      4 / n * ∑ j, w j ^ 2 := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (28000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hθ0' : (46 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := le_trans (by norm_num) hθ0
  have hθ1' : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100 := le_trans hθ1 (by norm_num)
  have hXi := XiS_theta hn16 hτ hθ0' hθ1 (by norm_num) hS
  have hXi4 := (Xi4_theta hn16 hτ hθ0' hθ1 (by norm_num) hS4).trans
    (gn_mono (n := n) (by norm_num : (1157 : ℝ) / 1000 * (10665 / 10000) * (55 / 100) ≤
      1157 / 1000 * (107 / 100) * (55 / 100)))
  have hXi8 := Xi8_theta hn16 hτ hθ0' hθ1 (by norm_num) hS8
  have heb := eb16_sharp_54 hn16 hτ hθ0 hθ1' hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0' hθ1' hG
  have c1 := centre16_int hn16 hτ hθ0' hθ1' hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 28000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 1157 / 1000 * (1067 / 1000) * (55 / 100)) (a := 1157 / 1000 * (107 / 100) * (55 / 100))
    (eb := 433 / 625) (xi := 221 / 1000) (e1 := 2081 / 2500) (e2 := 281 / 100000)
    (N22 := 18334 / 1000 / 28000) (q := 2 * (1157 / 1000 * (1067 / 1000) * (55 / 100)) / 28000) (sd := 111 / 250)
    (s := 2743 / 5000) (r := 15217 / 10000) (η := 7 / 25) (κ := 2351 / 500) (ρ := 493 / 100000)
    (by norm_num) c4 hXi hXi4 hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (2743 / 5000 - 111 / 250) ^ 8) ≤
      (1609 / 100 * (1157 / 1000 * (107 / 100) * (55 / 100) : ℝ)) ^ 4 / (28000 ^ 3 * (2743 / 5000 - 111 / 250) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The Agent frame bound `(4)/n`, every `n ≥ 28000`**: the split of second order on nine
pieces of the window `0.46 ≤ θ_in ≤ 0.55` (width `0.01`); on `EA16 D` and the events `SXi`,
`SXi4n`, `SXi8n`, `SSc`. Constants: `N_cov = 1.157·1.067·θ_hi`, `ξ = 0.221`, `e_b` from
the table of `Part160ScTab`. -/
theorem frameA3_28000 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n))
    (hE4 : E ⊆ agentEv D (SXi4n n)) (hE8 : E ⊆ agentEv D (SXi8n n))
    (hES : E ⊆ agentEv D (SSc n)) : FRAME_A_hyp D (4 / n) E := by
  intro c hc w
  obtain ⟨hτ, hlo46, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE4 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE8 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hES hc hτ

  by_cases h46 : thetaC c.1.2 (D.tau0 c) ≤ 47 / 100
  · exact framePiece_46 hn D hD c hτ hlo46 h46 hG hS hS4 hS8 hSS w
  have hlo47 : (47 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h46).le
  by_cases h47 : thetaC c.1.2 (D.tau0 c) ≤ 48 / 100
  · exact framePiece_47 hn D hD c hτ hlo47 h47 hG hS hS4 hS8 hSS w
  have hlo48 : (48 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h47).le
  by_cases h48 : thetaC c.1.2 (D.tau0 c) ≤ 49 / 100
  · exact framePiece_48 hn D hD c hτ hlo48 h48 hG hS hS4 hS8 hSS w
  have hlo49 : (49 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h48).le
  by_cases h49 : thetaC c.1.2 (D.tau0 c) ≤ 50 / 100
  · exact framePiece_49 hn D hD c hτ hlo49 h49 hG hS hS4 hS8 hSS w
  have hlo50 : (50 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h49).le
  by_cases h50 : thetaC c.1.2 (D.tau0 c) ≤ 51 / 100
  · exact framePiece_50 hn D hD c hτ hlo50 h50 hG hS hS4 hS8 hSS w
  have hlo51 : (51 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h50).le
  by_cases h51 : thetaC c.1.2 (D.tau0 c) ≤ 52 / 100
  · exact framePiece_51 hn D hD c hτ hlo51 h51 hG hS hS4 hS8 hSS w
  have hlo52 : (52 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h51).le
  by_cases h52 : thetaC c.1.2 (D.tau0 c) ≤ 53 / 100
  · exact framePiece_52 hn D hD c hτ hlo52 h52 hG hS hS4 hS8 hSS w
  have hlo53 : (53 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h52).le
  by_cases h53 : thetaC c.1.2 (D.tau0 c) ≤ 54 / 100
  · exact framePiece_53 hn D hD c hτ hlo53 h53 hG hS hS4 hS8 hSS w
  have hlo54 : (54 : ℝ) / 100 ≤ thetaC c.1.2 (D.tau0 c) := (not_le.mp h53).le
  exact framePiece_54 hn D hD c hτ hlo54 hθ1 hG hS hS4 hS8 hSS w

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 28000`.** For a design with the Agent centre of Part 154 and a `τ₀` that is a function of
the World data: IF the events `H`, `E₁` of the caller have charges with
`δ_hid + v_W/h_W² + δ_extra + 32/100000 ≤ 0.0063`, and on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the World
window (`τ₀ > 0`, `0.46 ≤ θ_in ≤ 0.55`), the World frame bound `1.377/n` and the Agent replacement
hold, THEN the program succeeds with probability at least `99/100`. The Agent frame bound
`(4)/n` is PROVED on 5 Agent events of total charge at most `32/100000`; the ledger
is that of `classifier_frame_4`. -/
theorem classifier_agentframe3_28000 (hn : 28000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 32 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hEv1 := events_with_EA16 hn16 D hτ hEv
  have hEv2 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (SXi_charge hn16) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (SXi4n_charge hn16) hEv2
  have hEv4 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (SXi8n_charge hn16) hEv3
  have hEv5 := events_with_agent D hτ (measurableSet_SSc n) (by norm_num)
    (SSc_charge_num hn16) hEv4
  have hsub1 := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hsub2 := goodSet_inter_subset H (E₁ ∩ EA16 D) (agentEv D (SXi n)) (HbarW D) hWL
  have hsub3 := goodSet_inter_subset H ((E₁ ∩ EA16 D) ∩ agentEv D (SXi n))
    (agentEv D (SXi4n n)) (HbarW D) hWL
  have hsub4 := goodSet_inter_subset H (((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩
    agentEv D (SXi4n n)) (agentEv D (SXi8n n)) (HbarW D) hWL
  have hsub5 := goodSet_inter_subset H ((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩
    agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n)) (agentEv D (SSc n)) (HbarW D) hWL
  have hsub := (((hsub5.trans hsub4).trans hsub3).trans hsub2).trans hsub1
  have hFA := frameA3_28000 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub2 (hsub3 (hsub4 (hsub5 hc)))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 (hsub5 hc))))
    (fun c hc => goodSet_inter_mem (hsub4 (hsub5 hc)))
    (fun c hc => goodSet_inter_mem (hsub5 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_4 hn D t hEv5 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **The paper's design and the paper's charges, every `n ≥ 28000`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe3_28000 (hn : 28000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
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
  classifier_agentframe3_28000 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv
    (by unfold δhidL vWL hWL δextraL; norm_num) hWin hFW hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms frameA3_28000
open BstLean.Part160 in
#print axioms classifier_agentframe3_28000
open BstLean.Part160 in
#print axioms classifier_paper_agentframe3_28000
