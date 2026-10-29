import BstLean.Part229Network
import BstLean.Part219Latitude

/-! The exact radial chain rule for a positively homogeneous scalar test. -/
namespace BstLean.Part229
open Real Matrix Filter Topology
open BstLean.Part130 BstLean.Part153
open BstLean.Part219 (dotLinear dotLinear_apply hasFDerivAt_nrm)

theorem homogeneous_euler {n : ℕ} {H : (Fin n → ℝ) → ℝ}
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, H (t • x) = t * H x)
    {y : Fin n → ℝ} (hH : DifferentiableAt ℝ H y) :
    fderiv ℝ H y y = H y := by
  have hc : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have hd := hH.hasFDerivAt.comp_hasDerivAt_of_eq 1 hc (by simp)
  have he : (fun t : ℝ => t * H y) =ᶠ[𝓝 1] (H ∘ fun t : ℝ => t • y) := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (hhom t ht.le y).symm
  have hm : HasDerivAt (fun t : ℝ => t * H y) (H y) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (H y)
  exact (hd.congr_of_eventuallyEq he).unique hm

theorem homogeneous_sphere_derivative {n : ℕ} {H : (Fin n → ℝ) → ℝ}
    (hhom : ∀ t : ℝ, 0 ≤ t → ∀ x, H (t • x) = t * H x)
    (c : Fin n → ℝ) (τ : ℝ) {ξ : Fin n → ℝ}
    (hy : normSq (c + τ • ξ) ≠ 0) (hH : DifferentiableAt ℝ H (c + τ • ξ))
    (v : Fin n → ℝ) :
    fderiv ℝ (sphereScalar c τ H) ξ v =
      (τ / nrm (c + τ • ξ)) *
        fderiv ℝ H (c + τ • ξ) (projT (sphPt (c + τ • ξ)) *ᵥ v) := by
  set y := c + τ • ξ
  have hN : nrm y ≠ 0 := (sqrt_pos.mpr
    (lt_of_le_of_ne (normSq_nonneg _) hy.symm)).ne'
  have hA : HasFDerivAt (fun x : Fin n → ℝ => c + τ • x)
      (τ • ContinuousLinearMap.id ℝ (Fin n → ℝ)) ξ :=
    ((hasFDerivAt_id ξ).const_smul τ).const_add c
  have hinv := (hasDerivAt_inv hN).comp_hasFDerivAt ξ ((hasFDerivAt_nrm hy).comp ξ hA)
  have hd := (hH.hasFDerivAt.comp ξ hA).fun_mul hinv
  have he : sphereScalar c τ H =ᶠ[𝓝 ξ]
      fun x => H (c + τ • x) * (nrm (c + τ • x))⁻¹ := by
    filter_upwards [(cont_ns c τ).continuousAt.eventually_ne hy] with x hx
    rw [sphereScalar, sphPt_eq' hx]
    rw [hhom _ (by positivity)]
    rw [one_div]
    change (nrm (c + τ • x))⁻¹ * H (c + τ • x) = _
    ring
  rw [(hd.congr_of_eventuallyEq he).fderiv]
  have hE := homogeneous_euler hhom hH
  rw [projT_mulVec_sj, sphPt_eq' hy]
  simp only [Function.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, dotLinear_apply,
    smul_eq_mul, dotProduct_smul, smul_dotProduct, map_sub, map_smul, hE,
    one_div]
  change _ = τ / nrm y *
    (fderiv ℝ H y v - ((nrm y)⁻¹ * (y ⬝ᵥ v)) * ((nrm y)⁻¹ * H y))
  dsimp only [y] at hN ⊢
  field_simp
  <;> ring

end BstLean.Part229
