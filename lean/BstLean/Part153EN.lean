import BstLean.Part153Energy
import BstLean.Part153Cen
import BstLean.Part150Norm2

/-!
# Part 153, item 2: Lemma EN assembled

* `GamS_eq_gO`: the energy `Γ` as a mean over `ξ` (`GamS`, Part153Op) is the row form `gO` of
  Part 150.
* **`EN_iii`**: Lemma EN (iii) at the parameters of the paper (`L_c = 12`, `δ_e = 0.011`,
  `n ≥ 8192`): if `A₁` is in `E_e` and in `E_sc` (`s_h² ≥ c_s·τ²`), `θ_in ≥ θ_lo`, and `A₂` is in
  `E_be`, then `e_b° = t_A|b°|²/γ_A ≤ 1 + 2δ_e − (1 − 1/π)(c_s/2)θ_lo`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150

/-- `Γ` as a mean over `ξ` is the row form `gO` of Part 150. -/
theorem GamS_eq_gO {m n : ℕ} (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (τ : ℝ) : GamS A₁ c τ = gO A₁ c τ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold GamS
  rw [← (gO_eq_gauss hm A₁ c τ).2]
  field_simp

/-- **Lemma EN (iii)** at `L_c = 12`, `δ_e = 11/1000`, `n ≥ 8192`. Hypotheses: `A₁ ∈ E_e`
(`hA`), `A₁ ∈ E_sc` (`hsc`), the window `θ_in ≥ θ_lo` (`hθ`), `A₂ ∈ E_be` (`hbe`).
Conclusion: `e_b° ≤ 1 + 2δ_e − (1 − 1/π)(c_s/2)θ_lo`. -/
theorem EN_iii {n : ℕ} (hn : 8192 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) {cs θlo : ℝ}
    (hρ : 0 < normSq c + (n : ℝ) * τ ^ 2)
    (hA : |√(GamS A₁ c τ) - ∫ A, √(GamS A c τ) ∂gaussMat (mA n) n (2 / (n : ℝ))| ≤
      √(2 * 12 * (2 / (n : ℝ))) * (√(2 / ((mA n : ℕ) : ℝ)) * √(normSq c + (n : ℝ) * τ ^ 2)))
    (hcs : 0 ≤ cs) (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    (hbe : Pb A₁ c τ A₂ ≤ ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
      √(2 * 12 * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ)) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      1 + 2 * (11 / 1000) - (1 - 1 / π) * (cs / 2) * θlo := by
  have hn1 : 1 ≤ n := by omega
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hE := Ee_delta_12 hn c τ hA
  rw [GamS_eq_gO hmA] at hE
  refine eb_le hn1 A₁ A₂ c τ hρ (by norm_num) hE hcs hsc hθ hbe ?_
  have hn0 : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have h12 : √(12 : ℝ) ≤ 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h1 : 4 * √(12 : ℝ) / n ≤ 16 / 8192 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    nlinarith
  have h2 : 4 * (12 : ℝ) / (n : ℝ) ^ 2 ≤ 48 / 8192 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  nlinarith

#print axioms GamS_eq_gO
#print axioms EN_iii

end BstLean.Part153
