import BstLean.Part218SquaredMoments
import BstLean.Part218RadialAngular
import BstLean.Part218NormVariance

/-! The Gaussian pair envelope applies to the actual sphere input norm kernel. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part105 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part214

theorem gaussian_relu_square_pair_unit {N : ℕ} {x y : Fin N → ℝ}
    (hx : normSq x = 1) (hy : normSq y = 1) :
    (∫ u, relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2 ∂stdGauss (Fin N)) =
      reluSquarePair (dotp x y) := by
  classical
  let A : Matrix (Fin 1 ⊕ Fin 1) (Fin N) ℝ :=
    Matrix.fromRows (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)
  have hc : |dotp x y| ≤ 1 := by
    simpa only [dotp] using BstLean.Part134.abs_dot_le_one hx hy
  have hA : A * A.transpose = Matrix.fromBlocks 1 (dotp x y • 1) (dotp x y • 1) 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j
    · simpa [A, Matrix.fromRows, Matrix.mul_apply, dotProduct, normSq, pow_two] using hx
    · simp [A, Matrix.fromRows, Matrix.mul_apply, dotProduct, dotp]
    · simp [A, Matrix.fromRows, Matrix.mul_apply, dotProduct, dotp, mul_comm]
    · simpa [A, Matrix.fromRows, Matrix.mul_apply, dotProduct, normSq, pow_two] using hy
  have hd := ouPair_of_cov hc A hA
  let f : ((Fin 1 → ℝ) × (Fin 1 → ℝ)) → ℝ := fun p => relu (p.1 0) ^ 2 * relu (p.2 0) ^ 2
  have mf : Measurable f := by dsimp [f]; unfold relu; fun_prop
  have hi := congrArg (fun μ => ∫ p, f p ∂μ) hd
  rw [integral_map (by fun_prop) mf.aestronglyMeasurable,
    integral_map (by unfold sC; fun_prop) mf.aestronglyMeasurable] at hi
  simpa only [f, A, reluSquarePair, Matrix.fromRows, Matrix.of_apply, Matrix.fromRows_mulVec, Sum.elim_inl, Sum.elim_inr,
    Matrix.mulVec, dotProduct, dotp] using hi

theorem sphere_relu_square_pair_unit {N : ℕ} (hN : 1 ≤ N) {x y : Fin N → ℝ}
    (hx : normSq x = 1) (hy : normSq y = 1) :
    (∫ u, relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2 ∂uniformSphere N) =
      reluSquarePair (dotp x y) / ((N : ℝ) * (N + 2)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have mf : Measurable (fun u => relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2) := by
    unfold dotp relu
    fun_prop
  have hh := gaussian_homogeneous hN 2 mf (by
    intro a ha u
    have he (z : Fin N → ℝ) : dotp z (a • u) = a * dotp z u := by
      unfold dotp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_comm, mul_left_comm]
    rw [he, he, relu_mul_of_nonneg ha, relu_mul_of_nonneg ha]
    ring)
  rw [gaussian_relu_square_pair_unit hx hy] at hh
  norm_num [BstLean.Part36.rhoD, Finset.prod_range_succ] at hh
  apply (eq_div_iff (by positivity : (N : ℝ) * (N + 2) ≠ 0)).mpr
  nlinarith [hh]

theorem normKernel_unit {N : ℕ} (hN : 1 ≤ N) {x y : Fin N → ℝ}
    (hx : normSq x = 1) (hy : normSq y = 1) :
    normKernel N (x, y) = squaredAngularB N (dotp x y) := by
  unfold normKernel squaredAngularB
  rw [sphere_relu_square_pair_unit hN hx hy, hx, hy, one_mul]

lemma normKernel_scale {N : ℕ} (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (x y : Fin N → ℝ) :
    normKernel N (a • x, b • y) = a ^ 2 * b ^ 2 * normKernel N (x, y) := by
  unfold normKernel
  simp only [dotp_smul_first, relu_mul_of_nonneg ha, relu_mul_of_nonneg hb, normSq_smul, mul_pow]
  have he : (fun u : Fin N → ℝ => (a ^ 2 * relu (dotp x u) ^ 2) *
      (b ^ 2 * relu (dotp y u) ^ 2)) =
      fun u => (a ^ 2 * b ^ 2) * (relu (dotp x u) ^ 2 * relu (dotp y u) ^ 2) := by
    funext u
    ring
  rw [he, integral_const_mul]
  ring

theorem normKernel_formula {N : ℕ} (hN : 1 ≤ N) (x y : Fin N → ℝ) :
    normKernel N (x, y) = normSq x * normSq y * squaredAngularB N (rowCos x y) := by
  by_cases hx0 : normSq x = 0
  · have hx := normSq_eq_zero hx0
    subst x
    simp [normKernel, normSq, dotp, relu]
  by_cases hy0 : normSq y = 0
  · have hy := normSq_eq_zero hy0
    subst y
    simp [normKernel, normSq, dotp, relu]
  have hxp : 0 < nrm x := sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg x) (Ne.symm hx0))
  have hyp : 0 < nrm y := sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy0))
  let x' := (nrm x)⁻¹ • x
  let y' := (nrm y)⁻¹ • y
  have hx' : normSq x' = 1 := by
    dsimp [x']; rw [normSq_smul, inv_pow, nrm_sq]; field_simp
  have hy' : normSq y' = 1 := by
    dsimp [y']; rw [normSq_smul, inv_pow, nrm_sq]; field_simp
  have hxx : nrm x • x' = x := by dsimp [x']; rw [smul_smul, mul_inv_cancel₀ hxp.ne', one_smul]
  have hyy : nrm y • y' = y := by dsimp [y']; rw [smul_smul, mul_inv_cancel₀ hyp.ne', one_smul]
  have hc : dotp x' y' = rowCos x y := by
    have he : dotp x' y' = (nrm x)⁻¹ * (nrm y)⁻¹ * dotp x y := by
      unfold x' y' dotp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    unfold rowCos
    ring
  have he := normKernel_scale (nrm x) (nrm y) hxp.le hyp.le x' y'
  rw [hxx, hyy, normKernel_unit hN hx' hy', hc, nrm_sq, nrm_sq] at he
  exact he

end BstLean.Part218
#print axioms BstLean.Part218.normKernel_unit
