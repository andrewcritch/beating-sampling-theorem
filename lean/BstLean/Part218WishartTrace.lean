import BstLean.Part218Wishart

/-! Exact trace moments include the covariance with the diagonal statistic. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part214

lemma radial_four_memLp {N : ℕ} (hN : 1 ≤ N) :
    MemLp (fun x : Fin N → ℝ => normSq x ^ 2) 2 (stdGauss (Fin N)) := by
  apply (memLp_two_iff_integrable_sq (measurable_normSq.pow_const 2).aestronglyMeasurable).mpr
  simpa only [← pow_mul] using gaussian_normSq_pow_integrable hN 4

lemma diagonal_memLp {N m : ℕ} (hN : 1 ≤ N) :
    MemLp (diagonalSum N m) 2 (gaussMat m N 1) := by
  rw [gaussMat_one_pi]
  exact memLp_finsetSum _ (fun i _ => (radial_four_memLp hN).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin m => stdGauss (Fin N)) i))

lemma wishart_pair_diagonal {N m : ℕ} (hN : 1 ≤ N) {i j : Fin m} (hij : i ≠ j) :
    covariance (fun x : Fin m → Fin N → ℝ => wishartKernel N (x i, x j))
      (fun x => normSq (x i) ^ 2) (Measure.pi fun _ : Fin m => stdGauss (Fin N)) =
      4 * (N : ℝ) * (N + 2) := by
  rw [pair_scalar_cov _ (wishartKernel_measurable N) (wishartKernel_memLp N)
    (measurable_normSq.pow_const 2) (radial_four_memLp hN) hij]
  have hp : (∫ p : (Fin N → ℝ) × (Fin N → ℝ),
      wishartKernel N p * normSq p.1 ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) =
      BstLean.Part36.rhoD N 3 := by
    simpa only [wishartKernel, mul_comm] using (pair_radial_moment hN 2).2
  rw [hp]
  change BstLean.Part36.rhoD N 3 -
    (∫ p, dotp p.2 p.1 ^ 2 ∂(stdGauss (Fin N)).prod (stdGauss (Fin N))) *
      (∫ x, normSq x ^ 2 ∂stdGauss (Fin N)) = _
  rw [(pair_kernel_moments N).2.1, gaussian_normSq_pow]
  simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  ring

lemma ordered_diagonal_covariance {N m : ℕ} (hN : 1 ≤ N)
    (p : Fin m × Fin m) (k : Fin m) :
    covariance (orderedRow (wishartKernel N) p) (fun x => normSq (x k) ^ 2)
      (Measure.pi fun _ : Fin m => stdGauss (Fin N)) =
      if p.1 = p.2 then 0 else
        (if k = p.1 then 4 * (N : ℝ) * (N + 2) else 0) +
        (if k = p.2 then 4 * (N : ℝ) * (N + 2) else 0) := by
  classical
  obtain ⟨i, j⟩ := p
  by_cases hij : i = j
  · simp [orderedRow, hij, covariance]
  change covariance (fun x : Fin m → Fin N → ℝ => if i = j then 0 else wishartKernel N (x i, x j))
    (fun x => normSq (x k) ^ 2) _ = _
  simp only [hij, ite_false, Prod.fst, Prod.snd]
  by_cases hki : k = i
  · subst k
    rw [wishart_pair_diagonal hN hij]
    simp [hij]
  by_cases hkj : k = j
  · subst k
    have hs : (fun x : Fin m → Fin N → ℝ => wishartKernel N (x i, x j)) =
        fun x => wishartKernel N (x j, x i) := by
      funext x; exact wishartKernel_symm _ _ _
    rw [hs, wishart_pair_diagonal hN (Ne.symm hij)]
    simp [Ne.symm hij]
  rw [pair_scalar_disjoint _ (wishartKernel_measurable N) (wishartKernel_memLp N)
    (measurable_normSq.pow_const 2) (radial_four_memLp hN) hij (Ne.symm hki) (Ne.symm hkj)]
  simp [hki, hkj]

/-- The mixed covariance counts both endpoints of every ordered pair. -/
theorem wishartOff_diagonal_covariance {N m : ℕ} (hN : 1 ≤ N) :
    covariance (wishartOff N m) (diagonalSum N m) (gaussMat m N 1) =
      8 * (m : ℝ) * ((m : ℝ) - 1) * N * (N + 2) := by
  classical
  rw [gaussMat_one_pi]
  change @covariance (Fin m → Fin N → ℝ) MeasurableSpace.pi
    (fun x => ∑ p, orderedRow (wishartKernel N) p x)
    (fun x => ∑ k, normSq (x k) ^ 2) (Measure.pi fun _ : Fin m => stdGauss (Fin N)) = _
  have ik : ∀ k : Fin m, MemLp (fun x : Fin m → Fin N → ℝ => normSq (x k) ^ 2) 2
      (Measure.pi fun _ : Fin m => stdGauss (Fin N)) := fun k =>
    (radial_four_memLp hN).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => stdGauss (Fin N)) k)
  rw [covariance_fun_sum_fun_sum (orderedRow_memLp _ (wishartKernel_memLp N)) ik]
  simp_rw [ordered_diagonal_covariance hN]
  rw [Fintype.sum_prod_type]
  have he : ∀ i j : Fin m, (∑ k : Fin m,
      if i = j then (0 : ℝ) else (if k = i then 4 * (N : ℝ) * (N + 2) else 0) +
        (if k = j then 4 * (N : ℝ) * (N + 2) else 0)) =
      8 * (N : ℝ) * (N + 2) - if i = j then 8 * (N : ℝ) * (N + 2) else 0 := by
    intro i j
    by_cases hij : i = j <;> simp [hij, Finset.sum_add_distrib] <;> ring
  simp_rw [he]
  simp [Finset.sum_sub_distrib]
  ring

noncomputable def wishartTrace (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  wishartOff N m M + diagonalSum N m M

theorem wishartTrace_entries (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) :
    wishartTrace N m M = ∑ i, ∑ j, dotp (M j) (M i) ^ 2 := by
  classical
  unfold wishartTrace wishartOff diagonalSum
  rw [Fintype.sum_prod_type]
  have he : ∀ i : Fin m, normSq (rowOf i M) ^ 2 =
      ∑ j : Fin m, if i = j then dotp (M j) (M i) ^ 2 else 0 := by
    intro i
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    unfold normSq dotp rowOf
    simp only [pow_two]
  simp_rw [he]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j <;> simp [orderedRow, wishartKernel, hij]

theorem wishartTrace_mean {N m : ℕ} (hN : 1 ≤ N) :
    (∫ M, wishartTrace N m M ∂gaussMat m N 1) = (m : ℝ) * N * (m + N + 1) := by
  unfold wishartTrace
  rw [integral_add ((wishartOff_memLp N m).integrable one_le_two) (diagonal_mean hN).1,
    wishartOff_mean, (diagonal_mean hN).2]
  ring

/-- The statistic is exactly the paper's `trace ((Xᵀ X)^2)`. -/
theorem wishartTrace_matrix (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) :
    wishartTrace N m M = ((M.transpose * M) ^ 2).trace := by
  have ht : ((M.transpose * M) ^ 2).trace = ((M * M.transpose) * (M * M.transpose)).trace := by
    calc
      _ = (M.transpose * (M * (M.transpose * M))).trace := by
        simp only [pow_two, Matrix.mul_assoc]
      _ = ((M * (M.transpose * M)) * M.transpose).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [wishartTrace_entries, ht]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ k, M i k * M j k) = ∑ k, M j k * M i k := by
    apply Finset.sum_congr rfl; intro k _; ring
  rw [he]
  simp only [dotp, pow_two]

/-- This is the full trace variance in P10e, including its mixed term. -/
theorem wishartTrace_variance {N m : ℕ} (hN : 1 ≤ N) :
    Var[wishartTrace N m; gaussMat m N 1] =
      (2 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (N : ℝ) ^ 2 + 6 * N) +
        8 * N * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) +
      8 * (m : ℝ) * N * (N + 2) * (N + 3) +
      2 * (8 * (m : ℝ) * ((m : ℝ) - 1) * N * (N + 2)) := by
  have he : wishartTrace N m = wishartOff N m + diagonalSum N m := rfl
  rw [he, variance_add (wishartOff_memLp N m) (diagonal_memLp hN),
    wishartOff_variance hN, wishartOff_diagonal_covariance hN,
    variance_eq_integral (measurable_diagonalSum N m).aemeasurable,
    (diagonal_mean hN).2, (diagonal_variance hN).2]
  ring

end BstLean.Part218
#print axioms BstLean.Part218.wishartOff_diagonal_covariance
#print axioms BstLean.Part218.wishartTrace_variance
