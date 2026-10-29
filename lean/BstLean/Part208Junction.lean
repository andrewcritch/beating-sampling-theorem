import BstLean.Part208Radius
import BstLean.Part199CoreWide

/-! Part 208: discharge the radius premise in the Part199 matrix theorem. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part182 BstLean.Part199
open BstLean.Part153 (Xi4)

/-- A uniform radius coefficient on the entire frontier interval and above it. -/
theorem Ew_frontier {n : ℕ} (hn : 4096 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ∫ ξ, BstLean.Part182.wN c τ ξ ∂stdGauss (Fin n) ≤
      (1024 / 1023 : ℝ) * thetaC c τ / n := by
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  obtain ⟨hθ0, hθ1⟩ := thetaC_bounds (by omega) c hτ
  have hsmall : thetaC c τ / n ≤ (1 / 4096 : ℝ) := by
    rw [div_le_iff₀ hn0]
    linarith
  have hd : (1023 / 1024 : ℝ) ≤ 1 - 4 * thetaC c τ / n := by
    rw [mul_div_assoc]
    linarith
  refine (Ew_paper (by omega) c hτ).trans ?_
  calc
    _ ≤ (thetaC c τ / n) / (1023 / 1024 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hd
    _ = _ := by ring

/-- The general core/wide matrix reduction now has no inverse-radius premise.
TI bad-mass and fourth-moment supplies remain explicit and unchanged. -/
theorem Dq_core_wide_paper_radius {n : ℕ} (hn : 6 ≤ n)
    (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ)
    {τ : ℝ} (hτ : 0 < τ) (w₀ w₁ : Window) (h10 : w₁.LE w₀)
    {lam₀ lam₁ M b₀ b₁ : ℝ} (hl₀ : 0 ≤ lam₀) (hl₁ : 0 ≤ lam₁)
    (hM : 0 ≤ M) (hθ : thetaC c τ < 1)
    (hr₀ : radiusMinus n (thetaC c τ) w₀ < 1)
    (hr₁ : radiusMinus n (thetaC c τ) w₁ < 1)
    (hX : Xi4 A₁ A₂ c τ ≤ M * (2 / (n : ℝ)) / n)
    (hb₀ : badMass n w₀.t w₀.z w₀.pair lam₀ ((c, τ), (A₁, A₂)) ≤ b₀)
    (hb₁ : badMass n w₁.t w₁.z w₁.pair lam₁ ((c, τ), (A₁, A₂)) ≤ b₁)
    (v : Fin (mA n) → ℝ) :
    Dq A₁ A₂ c τ v ≤ coreWideScalar n (thetaC c τ) w₀ w₁ lam₀ lam₁
      (1 - 4 * thetaC c τ / n)⁻¹ M b₀ b₁ * (2 / (n : ℝ)) / n * normSq v := by
  apply Dq_core_wide hn A₁ A₂ c hτ w₀ w₁ h10 hl₀ hl₁ hM hθ hr₀ hr₁
    (hX := hX) (hb₀ := hb₀) (hb₁ := hb₁)
  have h := Ew_paper (by omega) c hτ
  convert h using 1 <;> ring

end BstLean.Part208
