import BstLean.Part187All
import BstLean.Part160Theta
import BstLean.Part188R143HidC
import BstLean.Part188R143HidC2
import BstLean.Part188R153PPs4
import BstLean.Part188R153Final
import BstLean.Part188R154C16
import BstLean.Part188R154NumA16
import BstLean.Part188R154NumB16
import BstLean.Part188R154Num16
import BstLean.Part188R160Event
import BstLean.Part188R160Cov
import BstLean.Part188R160Cov8





namespace BstLean.Part188.Base160_R
open BstLean.Part160 BstLean.Part160.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part153 (XiS Xi4)

variable {n : ℕ}

/-- `Ξ ≤ 1.157·1.067·θh·γ_A/n` on `SXi`, for `0.46 ≤ θ_in ≤ θh ≤ 0.55`. -/
theorem XiS_theta (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXi n) :
    XiS A₁ A₂ c τ ≤ 1157 / 1000 * (1067 / 1000) * θh * (2 / (n : ℝ)) / n := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : XiS A₁ A₂ c τ ≤ 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ := h
  have h2 := Winv_le_theta hn c hτ hθ0 (hθ1.trans hθh)
  have h3 : 1067 / 1000 * (thetaC c τ / n) ≤ 1067 / 1000 * (θh / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hθ1 hn0.le) (by norm_num)
  have h4 : 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ ≤
      1157 / 1000 * (2 / (n : ℝ)) * (1067 / 1000 * (θh / (n : ℝ))) :=
    mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
  refine h1.trans (h4.trans (le_of_eq ?_))
  ring

/-- `Ξ₄ ≤ 1.157·1.0665·θh·γ_A/n` on `SXi4n`. -/
theorem Xi4_theta (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXi4n n) :
    Xi4 A₁ A₂ c τ ≤ 1157 / 1000 * (10665 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 2 A₁ A₂ c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 2 * WqN 2 c τ := h
  have h2 := W2_le_theta hn c hτ hθ0 (hθ1.trans hθh)
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1157 / 1000 * (10665 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have h3 : XqN 2 A₁ A₂ c τ ≤ B ^ 2 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [hB]; field_simp
  have h4 : √(XqN 2 A₁ A₂ c τ) ≤ B := by
    rw [← Real.sqrt_sq hB0]; exact Real.sqrt_le_sqrt h3
  rw [Xi4_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 1157 / 1000 * (10665 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(XqN 2 A₁ A₂ c τ) ≤
      2 / (n : ℝ) ^ 2 * (1157 / 1000 * (10665 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

/-- `Ξ₈ ≤ 1.157·1.07·θh·γ_A/n` on `SXi8n`. -/
theorem Xi8_theta (hn : 16200 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXi8n n) :
    Xi8 A₁ A₂ c τ ≤ 1157 / 1000 * (107 / 100) * θh * (2 / (n : ℝ)) / n := by
  have hnR : (16200 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 4 A₁ A₂ c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 4 * WqN 4 c τ := h
  have h2 := W4_le_theta hn c hτ hθ0 (hθ1.trans hθh)
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1157 / 1000 * (107 / 100) * thetaC c τ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have h3 : XqN 4 A₁ A₂ c τ ≤ (B ^ 2) ^ 2 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [hB]; field_simp
  have h4 : √(XqN 4 A₁ A₂ c τ) ≤ B ^ 2 := by
    rw [← Real.sqrt_sq (sq_nonneg B)]; exact Real.sqrt_le_sqrt h3
  have h4' : √(√(XqN 4 A₁ A₂ c τ)) ≤ B := by
    rw [← Real.sqrt_sq hB0]; exact Real.sqrt_le_sqrt h4
  rw [Xi8_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 1157 / 1000 * (107 / 100) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(√(XqN 4 A₁ A₂ c τ)) ≤
      2 / (n : ℝ) ^ 2 * (1157 / 1000 * (107 / 100) * θh) :=
    mul_le_mul_of_nonneg_left (h4'.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

end BstLean.Part188.Base160_R

