import BstLean.Part151S3

/-! Retain the noncentral exponential factor in the Gaussian Laplace transform. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

theorem laplace_one_exact {t : ℝ} (ht : 0 ≤ t) (a τ : ℝ) :
    ∫ x, exp (-(t * (a + τ * x) ^ 2)) ∂gaussianReal 0 1 =
      exp (-(t * a ^ 2 / (1 + 2 * t * τ ^ 2))) * (√(1 + 2 * t * τ ^ 2))⁻¹ := by
  have hpi := Real.pi_pos
  set b : ℝ := t * τ ^ 2 + 1 / 2 with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  set s : ℝ := t * a * τ / b with hs
  set K : ℝ := (√(2 * Real.pi))⁻¹ * exp (-(t * a ^ 2 / (2 * b))) with hK
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • exp (-(t * (a + τ * x) ^ 2)) =
      K * exp (-b * (x + s) ^ 2) := by
    intro x
    rw [smul_eq_mul, BstLean.Part131.pdf_eq, hK, mul_assoc, mul_assoc, ← Real.exp_add,
      ← Real.exp_add]
    congr 2
    rw [hs]
    field_simp
    rw [hb]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_add_right_eq_self (fun x => exp (-b * x ^ 2)) s,
    integral_gaussian b]
  have h2 : (√(2 * Real.pi))⁻¹ * √(Real.pi / b) = (√(1 + 2 * t * τ ^ 2))⁻¹ := by
    rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity)]
    congr 1
    rw [hb]
    field_simp
    ring
  have hden : 2 * b = 1 + 2 * t * τ ^ 2 := by rw [hb]; ring
  calc K * √(Real.pi / b) = exp (-(t * a ^ 2 / (2 * b))) *
      ((√(2 * Real.pi))⁻¹ * √(Real.pi / b)) := by rw [hK]; ring
    _ = _ := by rw [h2, hden]

theorem laplace_vector_exact {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ ξ, exp (-(t * normSq (c + τ • ξ))) ∂stdGauss (Fin n) =
      exp (-(t * normSq c / (1 + 2 * t * τ ^ 2))) *
        ((√(1 + 2 * t * τ ^ 2))⁻¹) ^ n := by
  have e : ∀ ξ : Fin n → ℝ, exp (-(t * normSq (c + τ • ξ))) =
      ∏ i, exp (-(t * (c i + τ * ξ i) ^ 2)) := by
    intro ξ
    rw [← Real.exp_sum]
    congr 1
    unfold normSq
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rfl
  simp_rw [e]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i x => exp (-(t * (c i + τ * x) ^ 2)))]
  simp_rw [laplace_one_exact ht]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 2
  unfold normSq
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.mul_sum]

theorem laplace_vector_integrable {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (c : Fin n → ℝ) (τ : ℝ) :
    Integrable (fun ξ => exp (-(t * normSq (c + τ • ξ)))) (stdGauss (Fin n)) := by
  letI : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hc : Continuous (fun ξ : Fin n → ℝ => exp (-(t * normSq (c + τ • ξ)))) := by
    unfold normSq
    fun_prop
  apply Integrable.of_bound hc.aestronglyMeasurable 1
  apply ae_of_all
  intro ξ
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg ht (normSq_nonneg _))
end BstLean.Part212
