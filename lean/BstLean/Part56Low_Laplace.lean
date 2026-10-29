import BstLean.Part56Defs
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace BstLean.Part56.LowLaplace

open MeasureTheory ProbabilityTheory BstLean.Part29

lemma gaussian_square_exp (u : ℝ) (hu : u < 1 / 2) :
    (∫ x : ℝ, Real.exp (u * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * u))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, smul_eq_mul]
  have he (x : ℝ) :
      (Real.sqrt (2 * Real.pi * 1))⁻¹ * Real.exp (-x ^ 2 / (2 * 1)) *
        Real.exp (u * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - 2 * u) / 2) * x ^ 2) := by
    simp only [mul_one]
    rw [mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  simp_rw [he]
  rw [integral_const_mul, integral_gaussian]
  have hpos : 0 < 1 - 2 * u := by linarith
  have hden : (1 - 2 * u) / 2 ≠ 0 := by positivity
  rw [show Real.pi / ((1 - 2 * u) / 2) = (2 * Real.pi) / (1 - 2 * u) by field_simp]
  rw [Real.sqrt_div (by positivity), ← mul_div_assoc,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 (by positivity)))]
  simp

lemma gaussian_square_exp_integrable (u : ℝ) (hu : u < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (u * x ^ 2)) (gaussianReal 0 1) := by
  by_contra h
  have he := gaussian_square_exp u hu
  rw [integral_undef h] at he
  have hpos : 0 < (Real.sqrt (1 - 2 * u))⁻¹ := by
    apply inv_pos.mpr
    apply Real.sqrt_pos.mpr
    linarith
  linarith

lemma gaussian_radial_laplace (m : ℕ) (L : ℝ) (hL : 0 < L) :
    (∫ z, Real.exp (-L * ∑ i, z i ^ 2) ∂stdGauss (Fin m)) =
      ((Real.sqrt (1 + 2 * L))⁻¹) ^ m := by
  classical
  have he (z : Fin m → ℝ) : Real.exp (-L * ∑ i, z i ^ 2) =
      ∏ i, Real.exp (-L * z i ^ 2) := by rw [← Real.exp_sum, ← Finset.mul_sum]
  simp_rw [he]
  rw [stdGauss, integral_fintype_prod_eq_pow (fun x : ℝ => Real.exp (-L * x ^ 2)), gaussian_square_exp (-L) (by linarith)]
  simp

lemma gaussian_radial_laplace_integrable (m : ℕ) (L : ℝ) (hL : 0 < L) :
    Integrable (fun z : Fin m → ℝ => Real.exp (-L * ∑ i, z i ^ 2)) (stdGauss (Fin m)) := by
  by_contra h
  have he := gaussian_radial_laplace m L hL
  rw [integral_undef h] at he
  have hp : 0 < ((Real.sqrt (1 + 2 * L))⁻¹) ^ m := by positivity
  linarith

lemma gaussian_cap_majorant_integrable (m : ℕ) (L : ℝ) (hL : 0 < L) :
    Integrable (fun p : ℝ × (Fin m → ℝ) => Real.exp (p.1 ^ 2 / 4 - L * ∑ i, p.2 i ^ 2))
      ((gaussianReal 0 1).prod (stdGauss (Fin m))) := by
  have h := (gaussian_square_exp_integrable (1 / 4) (by norm_num)).mul_prod
    (gaussian_radial_laplace_integrable m L hL)
  convert h using 1
  funext p
  rw [← Real.exp_add]
  congr 1
  ring

lemma gaussian_cap_majorant_integral (m : ℕ) (L : ℝ) (hL : 0 < L) :
    (∫ p : ℝ × (Fin m → ℝ), Real.exp (p.1 ^ 2 / 4 - L * ∑ i, p.2 i ^ 2)
      ∂(gaussianReal 0 1).prod (stdGauss (Fin m))) =
      Real.sqrt 2 * ((Real.sqrt (1 + 2 * L))⁻¹) ^ m := by
  have he (p : ℝ × (Fin m → ℝ)) :
      Real.exp (p.1 ^ 2 / 4 - L * ∑ i, p.2 i ^ 2) =
      Real.exp ((1 / 4 : ℝ) * p.1 ^ 2) * Real.exp (-L * ∑ i, p.2 i ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_prod_mul (fun a : ℝ => Real.exp ((1 / 4 : ℝ) * a ^ 2))
    (fun z : Fin m → ℝ => Real.exp (-L * ∑ i, z i ^ 2)),
    gaussian_square_exp (1 / 4) (by norm_num), gaussian_radial_laplace m L hL]
  have hs : (Real.sqrt (1 - 2 * (1 / 4 : ℝ)))⁻¹ = Real.sqrt 2 := by
    norm_num
  rw [hs]


end BstLean.Part56.LowLaplace
