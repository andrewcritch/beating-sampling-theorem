import BstLean.Part161Gauss
import BstLean.Part162LS

/-!
# Part 272: radial Gaussian rescaling

This is the inner Gaussian integral in the proposed coordinate-density proof.
The formula uses powers of `sqrt(v)` to avoid real-power conversions.
-/

namespace BstLean.Part272

open Real MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)
open BstLean.Part161 (gdN gd1 integral_affine)

/-- The centred density is a scalar Gaussian tilt. -/
theorem gdN_zero {k : ℕ} {v : ℝ} (hv : 0 < v) (w : Fin k → ℝ) :
    gdN 0 v w = (√v)⁻¹^k * exp (-(1/v-1)*(radF53 w)^2/2) := by
  unfold gdN gd1
  simp only [Pi.zero_apply, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 2
  rw [BstLean.Part162.radF_sq]
  have he : ∀ t : ℝ, -t^2/(2*v)+t^2/2 = (-(1/v-1)/2)*t^2 := by
    intro t
    field_simp [hv.ne']
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  ring

/-- Tilting the radius by `exp(-(1/v-1)R²/2)` multiplies its mean by `sqrt(v)^(k+1)`. -/
theorem radial_tilt {k : ℕ} {v : ℝ} (hv : 0 < v) :
    (∫ w, radF53 w * exp (-(1/v-1)*(radF53 w)^2/2) ∂stdGauss (Fin k)) =
      (√v)^(k+1) * ∫ w, radF53 w ∂stdGauss (Fin k) := by
  have h := integral_affine (ι := Fin k) 0 hv measurable_radF
  have he : ∀ w : Fin k → ℝ, radF53 (0+√v • w) = √v*radF53 w := by
    intro w
    rw [zero_add, BstLean.Part162.radF_eq_norm, WithLp.toLp_smul, norm_smul,
      ← BstLean.Part162.radF_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sqrt_nonneg v)]
  simp only [he, integral_const_mul, gdN_zero hv] at h
  have hprod : (fun w : Fin k → ℝ => radF53 w *
      ((√v)⁻¹^k * exp (-(1/v-1)*(radF53 w)^2/2))) =
      fun w => (√v)⁻¹^k * (radF53 w * exp (-(1/v-1)*(radF53 w)^2/2)) := by
    funext w; ring
  rw [hprod, integral_const_mul] at h
  have hs : √v ≠ 0 := (sqrt_pos.mpr hv).ne'
  have hp : (√v)^k ≠ 0 := pow_ne_zero _ hs
  rw [inv_pow] at h
  have hh := congrArg (fun t : ℝ => (√v)^k*t) h
  have hc : (√v)^k*((√v)^k)⁻¹ = 1 := mul_inv_cancel₀ hp
  have hh' : (√v)^k*(√v * ∫ w, radF53 w ∂stdGauss (Fin k)) =
      ∫ w, radF53 w * exp (-(1/v-1)*(radF53 w)^2/2) ∂stdGauss (Fin k) := by
    calc _ = ((√v)^k*((√v)^k)⁻¹)*
          (∫ w, radF53 w * exp (-(1/v-1)*(radF53 w)^2/2) ∂stdGauss (Fin k)) := by
            simpa only [mul_assoc] using hh
      _ = _ := by rw [hc, one_mul]
  rw [← hh', pow_succ]
  ring

end BstLean.Part272

#print axioms BstLean.Part272.radial_tilt
