import BstLean.Part208CoreWeight
import BstLean.Part182Geo

/-! Part 208: the actual core-weighted Gaussian second moment. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg sphPt)
open BstLean.Part53 (unitF53)
open BstLean.Part182 (OmegaS wN wN_nonneg integrable_wN measurableSet_OmegaS)

lemma wN_unit_sph {n : ℕ} (c f ξ : Fin n → ℝ) (τ : ℝ) :
    wN c τ ξ * (unitF53 (c + τ • ξ) ⬝ᵥ f) ^ 2 =
      wN c τ ξ * (sphPt (c + τ • ξ) ⬝ᵥ f) ^ 2 := by
  by_cases h : normSq (c + τ • ξ) = 0
  · simp [wN, h]
  · have he : sphPt (c + τ • ξ) = unitF53 (c + τ • ξ) := by
      simp only [sphPt, h, ↓reduceIte]
      rfl
    rw [he]

/-- The concrete core moment is derived from Gaussian symmetry, not assumed.
The latitude guard is a scalar inequality on the stated input window. -/
theorem omega_weighted_second {d : ℕ} (hd : 3 ≤ d) (u : Fin (d + 1) → ℝ)
    (hu : normSq u = 1) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (t0 z0 : ℝ) (f : Fin (d + 1) → ℝ) {sp : ℝ} (hsp : 0 ≤ sp)
    (hplane : ∀ Z r, axialCore (d + 1) t0 z0 Z r →
      (a + τ * Z) ^ 2 / ((a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2) ≤ sp) :
    (∫ ξ in OmegaS (a • u) t0 z0, wN (a • u) τ ξ *
      (sphPt (a • u + τ • ξ) ⬝ᵥ f) ^ 2 ∂stdGauss (Fin (d + 1))) ≤
      (∫ ξ, wN (a • u) τ ξ ∂stdGauss (Fin (d + 1))) *
        (sp * (u ⬝ᵥ f) ^ 2 + normSq f / d) := by
  let q := coreAxialWeight (d + 1) a τ t0 z0
  have hΩ := measurableSet_OmegaS (a • u) t0 z0
  have hwi := integrable_wN (n := d + 1) (by omega) (a • u) hτ
  have hqi : Integrable (axialWeight u q) (stdGauss (Fin (d + 1))) := by
    rw [show axialWeight u q = (OmegaS (a • u) t0 z0).indicator (wN (a • u) τ)
      from axialWeight_core_eq hu ha τ t0 z0]
    exact hwi.indicator hΩ
  have h := gaussian_rotated_second_le (by omega) u hu a τ f q
    (coreAxialWeight_measurable _ _ _ _ _) hqi
    (coreAxialWeight_nonneg _ _ _ _ _) (coreAxialWeight_plane _ _ _ _ _ hplane)
  have he : (∫ ξ, axialWeight u q ξ * (unitF53 (a • u + τ • ξ) ⬝ᵥ f) ^ 2
      ∂stdGauss (Fin (d + 1))) =
      ∫ ξ in OmegaS (a • u) t0 z0, wN (a • u) τ ξ *
        (sphPt (a • u + τ • ξ) ⬝ᵥ f) ^ 2 ∂stdGauss (Fin (d + 1)) := by
    rw [← integral_indicator hΩ]
    apply integral_congr_ae
    filter_upwards [] with ξ
    rw [show axialWeight u q = (OmegaS (a • u) t0 z0).indicator (wN (a • u) τ)
      from axialWeight_core_eq hu ha τ t0 z0]
    by_cases hξ : ξ ∈ OmegaS (a • u) t0 z0
    · simp only [indicator_of_mem hξ]
      exact wN_unit_sph (a • u) f ξ τ
    · simp only [indicator_of_notMem hξ, zero_mul]
  rw [he] at h
  have hmass : (∫ ξ, axialWeight u q ξ ∂stdGauss (Fin (d + 1))) ≤
      ∫ ξ, wN (a • u) τ ξ ∂stdGauss (Fin (d + 1)) := by
    apply integral_mono hqi hwi
    intro ξ
    rw [show axialWeight u q = (OmegaS (a • u) t0 z0).indicator (wN (a • u) τ)
      from axialWeight_core_eq hu ha τ t0 z0]
    by_cases hξ : ξ ∈ OmegaS (a • u) t0 z0
    · simp only [indicator_of_mem hξ, le_refl]
    · simp only [indicator_of_notMem hξ]
      exact wN_nonneg _ _ _
  refine h.trans ?_
  have hb := mul_le_mul_of_nonneg_left hmass
    (add_nonneg (mul_nonneg hsp (sq_nonneg (u ⬝ᵥ f)))
      (div_nonneg (normSq_nonneg f) (Nat.cast_nonneg d)))
  simpa only [mul_comm] using hb

end BstLean.Part208
