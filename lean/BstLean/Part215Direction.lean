import BstLean.Part215Transfer
import BstLean.Part160Dmat
import BstLean.Part188Interfaces

/-! The computed denominator is retained in the gradient and its transfer. -/
namespace BstLean.Part215
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)

lemma nrm_sub_swap {m : ℕ} (μ b : Fin m → ℝ) : nrm (b - μ) = nrm (μ - b) := by
  unfold nrm normSq
  congr 1
  exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring

/-- The coordinate keeps the computed centre in the numerator and denominator. -/
noncomputable def computedCoordinate {n m : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) (b : Fin m → ℝ) (ξ : Fin n → ℝ) : ℝ :=
  ((√(n : ℝ) * nrm b)⁻¹ • b) ⬝ᵥ hid2 A M (sphPt (c + τ • ξ))

/-- The standalone coordinate equals the existing retained-data coordinate, including zero centres. -/
theorem computedCoordinate_eq_centreCoordinate {n : ℕ}
    (D : BstLean.Part157.Design n) (c : BstLean.Part157.Ret n) :
    computedCoordinate c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) (D.bA c.1 c.2.1.1) =
      BstLean.Part188.centreCoordinate D c := by
  funext ξ
  unfold computedCoordinate BstLean.Part188.centreCoordinate BstLean.Part157.hStand
  rw [smul_dotProduct, smul_eq_mul, dotProduct_comm]
  simp only [dotProduct]
  ring

/-- This pointwise bound follows from the actual normalized network Jacobian. -/
theorem computed_gradient_bound {n m : ℕ} (hn : 1 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (b : Fin m → ℝ) :
    ∀ᵐ ξ ∂stdGauss (Fin n),
      BstLean.Part151.gradSq (computedCoordinate A M c τ b) ξ ≤
        τ ^ 2 * (normSq (((√(n : ℝ) * nrm b)⁻¹ • b) ᵥ*
          jacT A M (sphPt (c + τ • ξ))) * (normSq (c + τ • ξ))⁻¹) := by
  filter_upwards [ae_normSq_ne hn c hτ.ne', BstLean.Part151.lemmaJ_shift A M c hτ.ne']
    with ξ hne hJ
  exact BstLean.Part160.gradSq_dot_le hn A M c hτ _ ξ hne hJ

/-- A matrix transfer uses the full error and the same computed denominator. -/
theorem tangent_transfer {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
    (μ b : Fin m → ℝ) {a : ℝ} (ha : 0 ≤ a) (hb : 0 < nrm b) :
    a * nrm (Jᵀ *ᵥ b) ≤ a * nrm (Jᵀ *ᵥ μ) +
      (a * nrm b * opN J) * (nrm (μ - b) / nrm b) := by
  have he : Jᵀ *ᵥ b = Jᵀ *ᵥ μ + Jᵀ *ᵥ (b - μ) := by
    rw [Matrix.mulVec_sub]
    abel
  have h := (nrm_add_le (Jᵀ *ᵥ μ) (Jᵀ *ᵥ (b - μ))).trans
    (add_le_add le_rfl (nrm_mulVec_le Jᵀ (b - μ)))
  rw [opN_transpose, nrm_sub_swap] at h
  rw [he]
  have h' := mul_le_mul_of_nonneg_left h ha
  have hs : (a * nrm b * opN J) * (nrm (μ - b) / nrm b) =
      a * (opN J * nrm (μ - b)) := by field_simp [hb.ne']
  rw [hs]
  simpa only [mul_add] using h'

/-- The earlier full-centre estimate supplies the pointwise transfer coefficient. -/
theorem tangent_transfer_of_full {n m : ℕ} (J : Matrix (Fin m) (Fin n) ℝ)
    (μ b : Fin m → ℝ) {a N e ξ : ℝ} (ha : 0 ≤ a) (hN : 0 < N)
    (he : 0 < e) (hξ : 0 ≤ ξ) (hb : N * e ≤ normSq b)
    (hfull : normSq (μ - b) ≤ ξ) :
    a * nrm (Jᵀ *ᵥ b) ≤ a * nrm (Jᵀ *ᵥ μ) +
      (a * nrm b * opN J) * √(ξ / (N * e)) := by
  have hbN : 0 < nrm b := sqrt_pos.mpr (lt_of_lt_of_le (mul_pos hN he) hb)
  exact (tangent_transfer J μ b ha hbN).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (relative_centre_error μ b hN he hξ hb hfull)
      (mul_nonneg (mul_nonneg ha (nrm_nonneg b)) (opN_nonneg J))))

#print axioms computed_gradient_bound
#print axioms computedCoordinate_eq_centreCoordinate
#print axioms tangent_transfer
#print axioms tangent_transfer_of_full
end BstLean.Part215
