import BstLean.Part218InputVariance
import BstLean.Part218Ordered

/-! The input norm kernel has an exactly zero conditional row mean. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part105 BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part141

noncomputable def normKernel (N : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) : ℝ :=
  (∫ u, relu (dotp p.1 u) ^ 2 * relu (dotp p.2 u) ^ 2 ∂uniformSphere N) -
    normSq p.1 * normSq p.2 / (4 * (N : ℝ) ^ 2)

lemma gaussian_relu_square (u : Fin N → ℝ) :
    Integrable (fun y : Fin N → ℝ => relu (dotp y u) ^ 2) (stdGauss (Fin N)) := by
  simpa only [Real.sqrt_one, one_smul, ← pow_two, dotp] using
    (rowPair137 (v := 1) (by norm_num) u u).1

lemma gaussian_relu_square_unit {u : Fin N → ℝ} (hu : normSq u = 1) :
    (∫ y : Fin N → ℝ, relu (dotp y u) ^ 2 ∂stdGauss (Fin N)) = 1 / 2 := by
  have h := (rowPair137 (v := 1) (by norm_num) u u).2.1
  rw [kernelPhi_eq_psi, psi_unit _ hu hu] at h
  have he : dotp u u = 1 := by simpa only [dotp, normSq, pow_two] using hu
  rw [he, kappa_one] at h
  simpa only [Real.sqrt_one, one_smul, ← pow_two, one_mul, one_pow, dotp] using h

lemma normKernel_joint_integrable {N : ℕ} (hN : 1 ≤ N) (x : Fin N → ℝ) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      relu (dotp x p.2) ^ 2 * relu (dotp p.1 p.2) ^ 2)
      ((stdGauss (Fin N)).prod (uniformSphere N)) := by
  have := uniformSphere_isProbability N hN
  have hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      relu (dotp x p.1) ^ 2 * relu (dotp p.2 p.1) ^ 2) := by
    unfold dotp relu
    fun_prop
  have hi : Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      relu (dotp x p.1) ^ 2 * relu (dotp p.2 p.1) ^ 2)
      ((uniformSphere N).prod (stdGauss (Fin N))) := by
    rw [integrable_prod_iff hc.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall (fun u => (gaussian_relu_square u).const_mul (relu (dotp x u) ^ 2)), ?_⟩
    have he : ∀ᵐ u ∂uniformSphere N,
        (∫ y : Fin N → ℝ, ‖relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2‖
          ∂stdGauss (Fin N)) = relu (dotp x u) ^ 2 / 2 := by
      filter_upwards [uniformSphere_ae_sphere N] with u hu
      simp only [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      rw [integral_const_mul, gaussian_relu_square_unit hu]
      ring
    apply Integrable.congr (sphere_cont_integrable hN (show Continuous
      (fun u : Fin N → ℝ => relu (dotp x u) ^ 2 / 2) by unfold dotp relu; fun_prop))
    filter_upwards [he] with u hu
    exact hu.symm
  exact hi.swap

/-- This zero holds for every fixed first row, including the zero row. -/
theorem normKernel_conditional_zero {N : ℕ} (hN : 1 ≤ N) (x : Fin N → ℝ) :
    Integrable (fun y => normKernel N (x, y)) (stdGauss (Fin N)) ∧
      (∫ y, normKernel N (x, y) ∂stdGauss (Fin N)) = 0 := by
  have := uniformSphere_isProbability N hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := normKernel_joint_integrable hN x
  have i2 : Integrable (fun y : Fin N → ℝ => normSq x * normSq y / (4 * (N : ℝ) ^ 2))
      (stdGauss (Fin N)) := ((gauss_normSq N).1.const_mul _).div_const _
  refine ⟨hi.integral_prod_left.sub i2, ?_⟩
  unfold normKernel
  rw [integral_sub hi.integral_prod_left i2, ← integral_prod _ hi, integral_prod_symm _ hi]
  have he : ∀ᵐ u ∂uniformSphere N,
      (∫ y : Fin N → ℝ, relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2 ∂stdGauss (Fin N)) =
        relu (dotp x u) ^ 2 / 2 := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu
    rw [integral_const_mul, gaussian_relu_square_unit hu]
    ring
  have hx2 : (∫ u, relu (dotp x u) ^ 2 ∂uniformSphere N) = normSq x / (2 * (N : ℝ)) := sphere_relu_sq hN x
  rw [integral_congr_ae he, integral_div, hx2,
    integral_div, integral_const_mul, (gauss_normSq N).2]
  field_simp
  ring

end BstLean.Part218
#print axioms BstLean.Part218.normKernel_conditional_zero
