import BstLean.Part219Latitude
import BstLean.Part219Moments
import BstLean.Part219AxialUpper

/-! The latitude gradient and the ideal main term use the same radial envelope. -/
namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part153 BstLean.Part215

lemma latitude_tangent_identity {n : ℕ} (u y : Fin n → ℝ) (hy : normSq y ≠ 0) :
    projT (sphPt y) *ᵥ u = u - (u ⬝ᵥ y / normSq y) • y := by
  have hR : nrm y ≠ 0 := (sqrt_pos.mpr
    (lt_of_le_of_ne (normSq_nonneg _) hy.symm)).ne'
  rw [projT_mulVec_sj, sphPt_eq' hy, smul_dotProduct, smul_eq_mul, smul_smul,
    dotProduct_comm y u]
  congr 2
  change (1 / nrm y * (u ⬝ᵥ y)) * (1 / nrm y) = _
  rw [← nrm_sq y]
  field_simp

theorem latitude_gradient_exact {n : ℕ} (u c : Fin n → ℝ) (τ : ℝ) {ξ : Fin n → ℝ}
    (hy : normSq (c + τ • ξ) ≠ 0) :
    BstLean.Part151.gradSq (fun x => u ⬝ᵥ standPoint c τ x) ξ =
      radial c τ ξ ^ 2 * normSq (projT (standPoint c τ ξ) *ᵥ u) := by
  unfold BstLean.Part151.gradSq
  rw [latitude_derivative u c τ hy]
  simp only [ContinuousLinearMap.smul_apply, dotLinear_apply, dotProduct,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [standPoint, latitude_tangent_identity u _ hy]
  rfl

theorem latitude_tangent_envelope {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1)
    (a : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) {ξ : Fin n → ℝ}
    (hy : normSq (a • u + τ • ξ) ≠ 0) :
    radial (a • u) τ ξ * nrm (projT (standPoint (a • u) τ ξ) *ᵥ u) ≤
      latitudeEnvelope (a • u) τ ξ := by
  set y := a • u + τ • ξ
  have hY : 0 < normSq y := lt_of_le_of_ne (normSq_nonneg _) hy.symm
  have huu : u ⬝ᵥ u = 1 := by simpa only [normSq, dotProduct, ← sq] using hu
  have hdot : u ⬝ᵥ y = a + τ * (u ⬝ᵥ ξ) := by
    simp only [y, dotProduct_add, dotProduct_smul, huu, smul_eq_mul, mul_one]
  have hnorm : normSq y = a ^ 2 + τ ^ 2 * normSq ξ + 2 * a * τ * (u ⬝ᵥ ξ) :=
    normSq_axis_shift hu a τ ξ
  have ht : normSq (projT (sphPt y) *ᵥ u) =
      τ ^ 2 * (normSq ξ - (u ⬝ᵥ ξ) ^ 2) / normSq y := by
    rw [latitude_tangent_identity u y hy, normSq_sub_smul, hu, hdot]
    field_simp
    rw [hnorm]
    ring
  have hr : 0 ≤ radial (a • u) τ ξ := radial_nonneg _ hτ _
  have he : 0 ≤ latitudeEnvelope (a • u) τ ξ := latitudeEnvelope_nonneg _ _ _
  apply le_of_sq_le_sq _ he
  rw [mul_pow, nrm_sq]
  change (τ / nrm y) ^ 2 * normSq (projT (sphPt y) *ᵥ u) ≤
    (τ ^ 2 / normSq y * nrm ξ) ^ 2
  rw [div_pow, nrm_sq, ht, mul_pow, div_pow, nrm_sq]
  have hle : τ ^ 2 * (normSq ξ - (u ⬝ᵥ ξ) ^ 2) ≤ τ ^ 2 * normSq ξ := by
    nlinarith [mul_nonneg (sq_nonneg τ) (sq_nonneg (u ⬝ᵥ ξ))]
  have hh := mul_le_mul_of_nonneg_left hle (sq_nonneg τ)
  have hh' := div_le_div_of_nonneg_right hh (sq_nonneg (normSq y))
  convert hh' using 1 <;> ring

/-- The exact derivative is bounded by the envelope before integration. -/
theorem latitude_gradient_envelope {n : ℕ} {u : Fin n → ℝ} (hu : normSq u = 1)
    (a : ℝ) {τ : ℝ} (hτ : 0 ≤ τ) {ξ : Fin n → ℝ}
    (hy : normSq (a • u + τ • ξ) ≠ 0) :
    BstLean.Part151.gradSq (fun x => u ⬝ᵥ standPoint (a • u) τ x) ξ ≤
      latitudeEnvelope (a • u) τ ξ ^ 2 := by
  rw [latitude_gradient_exact u _ τ hy]
  have h := pow_le_pow_left₀ (mul_nonneg (radial_nonneg _ hτ _) (nrm_nonneg _))
    (latitude_tangent_envelope hu a hτ hy) 2
  simpa only [mul_pow, nrm_sq] using h

#print axioms latitude_gradient_exact
#print axioms latitude_tangent_envelope
#print axioms latitude_gradient_envelope
end BstLean.Part219
