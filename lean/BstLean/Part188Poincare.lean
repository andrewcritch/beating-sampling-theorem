import BstLean.Part170FlQ
import BstLean.Part153S

/-! The two gradient terms in WF, with the singular-input Poincare theorem. -/

namespace BstLean.Part188

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130

/-- The integrated gradient triangle retains both terms under the same distribution. -/
theorem gradient_pair_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (A B : X → ℝ)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x)
    (hAi : Integrable A μ) (hBi : Integrable B μ)
    (hABi : Integrable (fun x => √(A x) * √(B x)) μ)
    {N C : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hA : ∫ x, A x ∂μ ≤ N) (hB : ∫ x, B x ∂μ ≤ C) :
    (∫ x, (A x + 2 * (√(A x) * √(B x)) + B x) ∂μ) ≤ (√N + √C) ^ 2 := by
  have hA2 : Integrable (fun x => √(A x) ^ 2) μ := by
    simpa only [Real.sq_sqrt (hA0 _)] using hAi
  have hB2 : Integrable (fun x => √(B x) ^ 2) μ := by
    simpa only [Real.sq_sqrt (hB0 _)] using hBi
  have hCS := BstLean.Part170.int_cs hA2 hB2 hABi
  simp only [Real.sq_sqrt (hA0 _), Real.sq_sqrt (hB0 _)] at hCS
  have hM : √(∫ x, A x ∂μ) * √(∫ x, B x ∂μ) ≤ √N * √C :=
    mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [integral_add (f := fun x => A x + 2 * (√(A x) * √(B x))) (g := B)
      (hAi.add (hABi.const_mul 2)) hBi,
    integral_add (f := A) (g := fun x => 2 * (√(A x) * √(B x)))
      hAi (hABi.const_mul 2), integral_const_mul]
  nlinarith [Real.sq_sqrt hN, Real.sq_sqrt hC]

/-- The analytic covariance step from a Lipschitz extension and an actual derivative bound.
Constructing the extension and proving the derivative bound remain caller obligations. -/
theorem weighted_covariance_of_gradient {n : ℕ} (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (Φ : (Fin n → ℝ) → ℝ) {K : ℝ} (hK : 0 ≤ K) (hPhi : BstLean.Part148.EuLip Φ K)
    (A B : (Fin n → ℝ) → ℝ) (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x)
    (hAi : Integrable A (stdGauss (Fin n))) (hBi : Integrable B (stdGauss (Fin n)))
    (hABi : Integrable (fun x => √(A x) * √(B x)) (stdGauss (Fin n)))
    (hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ => Φ (sphPt (c + τ • ξ))) ξ (Pi.single i 1)) ^ 2 ≤
        A ξ + 2 * (√(A ξ) * √(B ξ)) + B ξ)
    (hinv : Integrable (fun ξ : Fin n → ℝ => (normSq (c + τ • ξ))⁻¹ ^ 2)
      (stdGauss (Fin n)))
    (hne : ∀ᵐ ξ ∂stdGauss (Fin n), normSq (c + τ • ξ) ≠ 0)
    {N C : ℝ} (hN : 0 ≤ N) (hC : 0 ≤ C)
    (hA : ∫ ξ, A ξ ∂stdGauss (Fin n) ≤ N)
    (hB : ∫ ξ, B ξ ∂stdGauss (Fin n) ≤ C) :
    Integrable (fun ξ => (Φ (sphPt (c + τ • ξ)) -
      ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ, (Φ (sphPt (c + τ • ξ)) -
      ∫ ξ', Φ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
        (√N + √C) ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hΓ := (hAi.add (hABi.const_mul 2)).add hBi
  have hPC := BstLean.Part153.lemmaS_grad c hτ hK hPhi hΓ hgrad hinv hne
  exact ⟨hPC.1, hPC.2.trans
    (gradient_pair_integral (stdGauss (Fin n)) A B hA0 hB0 hAi hBi hABi hN hC hA hB)⟩

end BstLean.Part188
