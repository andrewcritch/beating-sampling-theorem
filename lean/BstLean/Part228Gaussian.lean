import BstLean.Part212Laplace
import BstLean.Part152LM

/-! The noncentral square transform allows either sign of the parameter. -/
namespace BstLean.Part228
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)

theorem square_transform {t a τ : ℝ} (hd : 0 < 1 - 2 * t * τ ^ 2) :
    Integrable (fun x : ℝ => exp (t * (a + τ * x) ^ 2)) (gaussianReal 0 1) ∧
    (∫ x, exp (t * (a + τ * x) ^ 2) ∂gaussianReal 0 1) =
      exp (t * a ^ 2 / (1 - 2 * t * τ ^ 2)) * (√(1 - 2 * t * τ ^ 2))⁻¹ := by
  let b := 1 / 2 - t * τ ^ 2
  have hb : 0 < b := by dsimp [b]; linarith
  let s := -(t * a * τ / b)
  let K := (√(2 * π))⁻¹ * exp (t * a ^ 2 / (2 * b))
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x • exp (t * (a + τ * x) ^ 2)) =
      fun x => K * exp (-b * (x + s) ^ 2) := by
    funext x
    rw [smul_eq_mul, BstLean.Part131.pdf_eq]
    dsimp [K]
    rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]
    congr 2
    dsimp [s]
    field_simp
    dsimp [b]
    ring
  constructor
  · rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    have he' : (fun x : ℝ => (gaussianPDF 0 1 x).toReal • exp (t * (a + τ * x) ^ 2)) =
        fun x => gaussianPDFReal 0 1 x • exp (t * (a + τ * x) ^ 2) := by
      funext x
      rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    rw [he', he]
    exact ((integrable_exp_neg_mul_sq hb).comp_add_right s).const_mul K
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero, he,
      integral_const_mul, integral_add_right_eq_self (fun x => exp (-b * x ^ 2)) s,
      integral_gaussian b]
    have h2 : (√(2 * π))⁻¹ * √(π / b) = (√(1 - 2 * t * τ ^ 2))⁻¹ := by
      rw [← sqrt_inv, ← sqrt_inv, ← sqrt_mul (by positivity)]
      congr 1
      dsimp [b]
      field_simp <;> ring
    have hden : 2 * b = 1 - 2 * t * τ ^ 2 := by dsimp [b]; ring
    calc K * √(π / b) = exp (t * a ^ 2 / (2 * b)) *
        ((√(2 * π))⁻¹ * √(π / b)) := by dsimp [K]; ring
      _ = _ := by rw [h2, hden]

/-- The central vector transform has no restriction on the sign of `t`. -/
theorem central_transform (d : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : Fin d → ℝ => exp (t * normSq x)) (stdGauss (Fin d)) ∧
    (∫ x, exp (t * normSq x) ∂stdGauss (Fin d)) = (√(1 - 2 * t))⁻¹ ^ d := by
  have he : (fun x : Fin d → ℝ => exp (t * normSq x)) =
      fun x => ∏ i, exp (t * x i ^ 2) := by
    funext x
    rw [← exp_sum]
    congr 1
    exact Finset.mul_sum _ _ _
  rw [he]
  constructor
  · exact MeasureTheory.Integrable.fintype_prod (fun _ => (BstLean.Part152.gauss_mgf_sq ht).1)
  · unfold stdGauss
    rw [integral_fintype_prod_eq_prod (fun (_ : Fin d) x => exp (t * x ^ 2))]
    simp_rw [(BstLean.Part152.gauss_mgf_sq ht).2]
    simp
end BstLean.Part228
