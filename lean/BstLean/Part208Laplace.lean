import BstLean.Part151S3

/-! Part 208: exact noncentral Gaussian Laplace transform. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

/-- The exact transform retains the squared centre. -/
theorem laplace_one_exact {t : ℝ} (ht : 0 ≤ t) (a τ : ℝ) :
    ∫ x, exp (-(t * (a + τ * x) ^ 2)) ∂gaussianReal 0 1 =
      (√(1 + 2 * t * τ ^ 2))⁻¹ * exp (-(t * a ^ 2 / (1 + 2 * t * τ ^ 2))) := by
  set b : ℝ := t * τ ^ 2 + 1 / 2 with hb
  have hb0 : 0 < b := by rw [hb]; positivity
  set s : ℝ := t * a * τ / b with hs
  set K : ℝ := (√(2 * Real.pi))⁻¹ * exp (-(t * a ^ 2 / (2 * b))) with hK
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  have e : ∀ x : ℝ, gaussianPDFReal 0 1 x • exp (-(t * (a + τ * x) ^ 2)) =
      K * exp (-b * (x + s) ^ 2) := by
    intro x
    rw [smul_eq_mul, BstLean.Part131.pdf_eq, hK, mul_assoc, mul_assoc, ← exp_add,
      ← exp_add]
    congr 2
    rw [hs]
    field_simp
    rw [hb]
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_add_right_eq_self (fun x => exp (-b * x ^ 2)) s,
    integral_gaussian b]
  have h2 : (√(2 * Real.pi))⁻¹ * √(Real.pi / b) = (√(1 + 2 * t * τ ^ 2))⁻¹ := by
    rw [← sqrt_inv, ← sqrt_inv, ← sqrt_mul (by positivity)]
    congr 1
    rw [hb]
    field_simp
    ring
  rw [hK, mul_right_comm, h2]
  congr 2
  rw [hb]
  ring

/-- Independent coordinates give the exact vector transform. -/
theorem laplace_vec_exact {n : ℕ} {t : ℝ} (ht : 0 ≤ t) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ ξ, exp (-(t * normSq (c + τ • ξ))) ∂stdGauss (Fin n) =
      ((√(1 + 2 * t * τ ^ 2))⁻¹) ^ n *
        exp (-(t * normSq c / (1 + 2 * t * τ ^ 2))) := by
  have e : ∀ ξ : Fin n → ℝ, exp (-(t * normSq (c + τ • ξ))) =
      ∏ i, exp (-(t * (c i + τ * ξ i) ^ 2)) := by
    intro ξ
    rw [← exp_sum]
    congr 1
    unfold normSq
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rfl
  simp_rw [e]
  unfold stdGauss
  rw [integral_fintype_prod_eq_prod (fun i x => exp (-(t * (c i + τ * x) ^ 2)))]
  simp_rw [laplace_one_exact ht]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← exp_sum]
  congr 2
  simp [normSq, Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum]

end BstLean.Part208
