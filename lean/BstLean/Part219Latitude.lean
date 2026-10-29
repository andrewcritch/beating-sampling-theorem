import BstLean.Part219Axial
import BstLean.Part167Grad

/-! The exact latitude derivative retains the tangential factor. -/
namespace BstLean.Part219
open MeasureTheory Real Matrix Filter Topology
open BstLean.Part130 BstLean.Part153 BstLean.Part215

noncomputable def dotLinear {n : ℕ} (u : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, u i • ContinuousLinearMap.proj i

lemma dotLinear_apply {n : ℕ} (u x : Fin n → ℝ) : dotLinear u x = u ⬝ᵥ x := by
  simp [dotLinear, dotProduct]

lemma hasFDerivAt_nrm {n : ℕ} {y : Fin n → ℝ} (hy : normSq y ≠ 0) :
    HasFDerivAt nrm ((nrm y)⁻¹ • dotLinear y) y := by
  obtain ⟨L, hL, he⟩ := BstLean.Part167.hasFDerivAt_nrm_mulVec
    (1 : Matrix (Fin n) (Fin n) ℝ) (by simpa using hy)
  have heq : L = (nrm y)⁻¹ • dotLinear y := by
    ext d
    rw [he]
    simp only [Matrix.one_mulVec, Matrix.vecMul_one, ContinuousLinearMap.smul_apply,
      dotLinear_apply, smul_eq_mul]
    unfold BstLean.Part166.bhat
    simp only [Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum, mul_assoc, nrm]
  change HasFDerivAt (fun z => √(normSq z)) ((nrm y)⁻¹ • dotLinear y) y
  simpa only [Matrix.one_mulVec, heq] using hL

/-- The derivative of a latitude in the original Euclidean coordinates. -/
theorem latitude_derivative {n : ℕ} (u c : Fin n → ℝ) (τ : ℝ) {ξ : Fin n → ℝ}
    (hy : normSq (c + τ • ξ) ≠ 0) :
    fderiv ℝ (fun x => u ⬝ᵥ standPoint c τ x) ξ =
      (τ / nrm (c + τ • ξ)) • dotLinear
        (u - ((u ⬝ᵥ (c + τ • ξ)) / normSq (c + τ • ξ)) • (c + τ • ξ)) := by
  set y := c + τ • ξ
  have hN : nrm y ≠ 0 := (sqrt_pos.mpr
    (lt_of_le_of_ne (normSq_nonneg _) hy.symm)).ne'
  have hA : HasFDerivAt (fun x : Fin n → ℝ => c + τ • x)
      (τ • ContinuousLinearMap.id ℝ (Fin n → ℝ)) ξ :=
    ((hasFDerivAt_id ξ).const_smul τ).const_add c
  have hinv := (hasDerivAt_inv hN).comp_hasFDerivAt ξ ((hasFDerivAt_nrm hy).comp ξ hA)
  have hd := ((dotLinear u).hasFDerivAt.comp ξ hA).fun_mul hinv
  have hlocal : (fun x => u ⬝ᵥ standPoint c τ x) =ᶠ[𝓝 ξ]
      fun x => dotLinear u (c + τ • x) * (nrm (c + τ • x))⁻¹ := by
    have he : ∀ᶠ x in 𝓝 ξ, normSq (c + τ • x) ≠ 0 :=
      (cont_ns c τ).continuousAt.eventually_ne hy
    filter_upwards [he] with x hx
    rw [dotLinear_apply, standPoint, sphPt_eq' hx, dotProduct_smul, smul_eq_mul]
    change 1 / nrm (c + τ • x) * (u ⬝ᵥ (c + τ • x)) = _
    ring
  rw [(hd.congr_of_eventuallyEq hlocal).fderiv]
  ext d
  simp only [Function.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, dotLinear_apply, smul_eq_mul,
    dotProduct_smul, smul_dotProduct, sub_dotProduct]
  change _ = τ / nrm y * (u ⬝ᵥ d - (u ⬝ᵥ y / normSq y) * (y ⬝ᵥ d))
  rw [← nrm_sq y]
  dsimp only [y] at hN ⊢
  field_simp
  <;> ring

#print axioms latitude_derivative
end BstLean.Part219
