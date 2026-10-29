import BstLean.Part208PlaneGuard
import BstLean.Part208Restricted

/-! Part 208: the concrete restricted tangential row estimate. -/
namespace BstLean.Part208
open MeasureTheory Real Matrix Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part153 (nrm nrm_sq abs_dot_le_nrm)
open BstLean.Part182

/-- The good-pair row can depend on Agent weights. Only its overlap denominator
is used before the numerator is extended to the axially symmetric input set. -/
theorem omega_tangent_row {d : ℕ} (hd : 3 ≤ d) (u x f : Fin (d + 1) → ℝ)
    (hu : normSq u = 1) (hx : normSq x = 1) (hf : x ⬝ᵥ f = 0)
    {a τ t0 z0 cp sm : ℝ} (ha : 0 < a) (hτ : 0 < τ) (ht : 0 ≤ t0)
    (hR : 0 < axialRadiusLower (d + 1) a τ t0 z0)
    (hcp : cp ^ 2 < 1) (hsm : sm ≤ (u ⬝ᵥ x) ^ 2)
    (H : Set (Fin (d + 1) → ℝ)) (hHm : MeasurableSet H)
    (hHΩ : H ⊆ OmegaS (a • u) t0 z0)
    (hc : ∀ ξ ∈ H, (x ⬝ᵥ sphPt (a • u + τ • ξ)) ^ 2 ≤ cp ^ 2) :
    (∫ ξ in H, wN (a • u) τ ξ * (eTan x (sphPt (a • u + τ • ξ)) ⬝ᵥ f) ^ 2
      ∂stdGauss (Fin (d + 1))) ≤
      (∫ ξ, wN (a • u) τ ξ ∂stdGauss (Fin (d + 1))) *
        ((axialPlaneUpper (d + 1) a τ t0 z0 * (1 - sm) + 1 / (d : ℝ)) /
          (1 - cp ^ 2)) * normSq f := by
  let X := fun ξ : Fin (d + 1) → ℝ => sphPt (a • u + τ • ξ)
  have hXm : Measurable X := measurable_sphPt.comp (by fun_prop)
  have hdotm : Measurable (fun ξ => X ξ ⬝ᵥ f) := by
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hXm).mul measurable_const
  have hdotb : ∀ ξ, (X ξ ⬝ᵥ f) ^ 2 ≤ normSq f := by
    intro ξ
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_dot_le_nrm (X ξ) f) 2
    rw [sq_abs, mul_pow, nrm_sq, nrm_sq, normSq_sphPt (by omega), one_mul] at h
    exact h
  have hwi := integrable_wN (n := d + 1) (by omega) (a • u) hτ
  have hi := hwi.mul_bdd (hdotm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdotb ξ)
  have hiΩ := hi.indicator (measurableSet_OmegaS (a • u) t0 z0)
  have htm : Measurable (fun ξ => wN (a • u) τ ξ * (eTan x (X ξ) ⬝ᵥ f) ^ 2) := by
    apply (measurable_wN _ _).mul
    unfold eTan dotProduct
    fun_prop
  have hden : 0 < 1 - cp ^ 2 := by linarith
  have hiH : Integrable (H.indicator (fun ξ => wN (a • u) τ ξ *
      (eTan x (X ξ) ⬝ᵥ f) ^ 2)) (stdGauss (Fin (d + 1))) := by
    apply Integrable.mono' (hwi.mul_const (normSq f / (1 - cp ^ 2)))
      (htm.indicator hHm).aestronglyMeasurable
    filter_upwards [] with ξ
    rw [Real.norm_eq_abs]
    by_cases hξ : ξ ∈ H
    · rw [indicator_of_mem hξ, abs_of_nonneg (mul_nonneg (wN_nonneg _ _ _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left
        ((tangent_pair_sq hf hcp (hc ξ hξ)).trans
          (div_le_div_of_nonneg_right (hdotb ξ) hden.le)) (wN_nonneg _ _ _)
    · rw [indicator_of_notMem hξ, abs_zero]
      exact mul_nonneg (wN_nonneg _ _ _) (div_nonneg (normSq_nonneg _) hden.le)
  have hmoment := omega_weighted_second_closed hd u hu ha hτ ht hR f
  rw [← integral_indicator (measurableSet_OmegaS (a • u) t0 z0)] at hmoment
  have h := restricted_tangent_row (stdGauss (Fin (d + 1))) (by omega) u x f X
    (wN (a • u) τ) (OmegaS (a • u) t0 z0) H hHΩ hu hx hf hcp
    (div_nonneg (sq_nonneg _) hR.le)
    (integral_nonneg (fun ξ => wN_nonneg _ _ ξ)) hsm (wN_nonneg _ _) hc hiH hiΩ
    (by simpa only [X, axialPlaneUpper, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hmoment)
  rw [integral_indicator hHm] at h
  simpa only [X, axialPlaneUpper, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h

end BstLean.Part208
