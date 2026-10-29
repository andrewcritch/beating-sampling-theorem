import BstLean.Part208CoreMoment

/-! Part 208: explicit scalar guards for the weighted latitude source. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq sphPt)
open BstLean.Part182 (OmegaS wN)

noncomputable def axialRadiusLower (n : ℕ) (a τ t0 z0 : ℝ) : ℝ :=
  a ^ 2 + τ ^ 2 * ((n : ℝ) - 2 * √((n : ℝ) * z0)) - 2 * a * τ * t0

noncomputable def axialPlaneUpper (n : ℕ) (a τ t0 z0 : ℝ) : ℝ :=
  (a + τ * t0) ^ 2 / axialRadiusLower n a τ t0 z0

/-- The radius lower guard and the longitudinal cutoff give the latitude upper bound. -/
theorem axialCore_plane_bound (n : ℕ) {a τ t0 z0 : ℝ}
    (ha : 0 ≤ a) (hτ : 0 ≤ τ) (ht : 0 ≤ t0)
    (hR : 0 < axialRadiusLower n a τ t0 z0) {Z r : ℝ}
    (h : axialCore n t0 z0 Z r) :
    (a + τ * Z) ^ 2 / ((a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2) ≤
      axialPlaneUpper n a τ t0 z0 := by
  obtain ⟨hZ, hlow, _⟩ := h
  have hZlo := (abs_le.mp hZ).1
  have hD : axialRadiusLower n a τ t0 z0 ≤ (a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hlow (sq_nonneg τ)
    have h2 := mul_le_mul_of_nonneg_left hZlo (mul_nonneg ha hτ)
    unfold axialRadiusLower
    nlinarith only [h1, h2]
  have hnum : (a + τ * Z) ^ 2 ≤ (a + τ * t0) ^ 2 := by
    have h1 : |a + τ * Z| ≤ a + τ * t0 := by
      refine (abs_add_le a (τ * Z)).trans ?_
      rw [abs_of_nonneg ha, abs_mul, abs_of_nonneg hτ]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hZ hτ)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h1 2
  unfold axialPlaneUpper
  calc
    _ ≤ (a + τ * t0) ^ 2 / ((a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2) :=
      div_le_div_of_nonneg_right hnum (hR.le.trans hD)
    _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hR hD

/-- The actual core moment now needs only a positive scalar radius lower bound. -/
theorem omega_weighted_second_closed {d : ℕ} (hd : 3 ≤ d) (u : Fin (d + 1) → ℝ)
    (hu : normSq u = 1) {a τ t0 z0 : ℝ} (ha : 0 < a) (hτ : 0 < τ) (ht : 0 ≤ t0)
    (hR : 0 < axialRadiusLower (d + 1) a τ t0 z0) (f : Fin (d + 1) → ℝ) :
    (∫ ξ in OmegaS (a • u) t0 z0, wN (a • u) τ ξ *
      (sphPt (a • u + τ • ξ) ⬝ᵥ f) ^ 2 ∂stdGauss (Fin (d + 1))) ≤
      (∫ ξ, wN (a • u) τ ξ ∂stdGauss (Fin (d + 1))) *
        (axialPlaneUpper (d + 1) a τ t0 z0 * (u ⬝ᵥ f) ^ 2 + normSq f / d) := by
  apply omega_weighted_second hd u hu ha hτ t0 z0 f
  · exact div_nonneg (sq_nonneg _) hR.le
  · intro Z r h
    exact axialCore_plane_bound (d + 1) ha.le hτ.le ht hR h

end BstLean.Part208
