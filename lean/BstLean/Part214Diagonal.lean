import BstLean.Part214Variance
import BstLean.Part41Error
import BstLean.Part162Dir

/-! Exact diagonal Wishart moments for arbitrary positive dimensions and widths. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part137

lemma gaussian_normSq_pow_integrable {N : ℕ} (hN : 1 ≤ N) (k : ℕ) :
    Integrable (fun ξ : Fin N → ℝ => normSq ξ ^ k) (stdGauss (Fin N)) := by
  have : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have he : ∀ ξ : Fin N → ℝ, BstLean.Part53.radF53 ξ ^ (2 * k) = normSq ξ ^ k := by
    intro ξ
    rw [pow_mul, BstLean.Part162.radF_sq]
    rfl
  simpa only [he] using (BstLean.Part162.integrable_radF_pow (d := N) (2 * k))

lemma gaussian_normSq_pow (N k : ℕ) :
    (∫ ξ : Fin N → ℝ, normSq ξ ^ k ∂stdGauss (Fin N)) =
      BstLean.Part36.rhoD N k := by
  have he : ∀ ξ : Fin N → ℝ, √(∑ i, ξ i ^ 2) ^ (2 * k) = normSq ξ ^ k := by
    intro ξ
    rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rfl
  have h := BstLean.Part41.p1_gauss_norm_moment (ι := Fin N) k
  simpa only [he, Fintype.card_fin] using h

noncomputable def diagonalSum (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  ∑ i, normSq (rowOf i M) ^ 2

lemma measurable_diagonalSum (N m : ℕ) : Measurable (diagonalSum N m) := by
  unfold diagonalSum
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_normSq.comp (measurable_rowOf i)).pow_const 2

/-- The paper's standard-row `B₁` has the exact mean `m N (N+2)`. -/
theorem diagonal_mean {N m : ℕ} (hN : 1 ≤ N) :
    Integrable (diagonalSum N m) (gaussMat m N 1) ∧
    (∫ M, diagonalSum N m M ∂gaussMat m N 1) =
      (m : ℝ) * N * (N + 2) := by
  classical
  have hi : ∀ i : Fin m, Integrable (fun M => normSq (rowOf i M) ^ 2)
      (gaussMat m N 1) := by
    intro i
    apply (row_integrable_iff 1 i (measurable_normSq.pow_const 2)).mpr
    simpa using gaussian_normSq_pow_integrable hN 2
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  unfold diagonalSum
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [row_integral 1 _ (measurable_normSq.pow_const 2)]
  simp only [sqrt_one, one_smul]
  rw [gaussian_normSq_pow]
  simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  ring

/-- The paper's standard-row `B₁` has variance `8 m N (N+2)(N+3)`. -/
theorem diagonal_variance {N m : ℕ} (hN : 1 ≤ N) :
    Integrable (fun M => (diagonalSum N m M - (m : ℝ) * N * (N + 2)) ^ 2)
      (gaussMat m N 1) ∧
    (∫ M, (diagonalSum N m M - (m : ℝ) * N * (N + 2)) ^ 2
      ∂gaussMat m N 1) = 8 * (m : ℝ) * N * (N + 2) * (N + 3) := by
  have hi : Integrable (fun ξ : Fin N → ℝ => (normSq (√(1 : ℝ) • ξ) ^ 2) ^ 2)
      (stdGauss (Fin N)) := by
    simpa only [sqrt_one, one_smul, ← pow_mul] using gaussian_normSq_pow_integrable hN 4
  have h := rows_variance_eq (m := m) 1 (fun ξ : Fin N → ℝ => normSq ξ ^ 2)
    (measurable_normSq.pow_const 2) hi
  simp only [sqrt_one, one_smul, ← pow_mul] at h
  rw [gaussian_normSq_pow N 2, gaussian_normSq_pow N 4] at h
  have he2 : BstLean.Part36.rhoD (N : ℝ) 2 = (N : ℝ) * (N + 2) := by
    simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  rw [he2] at h
  change Integrable (fun M => (diagonalSum N m M - (m : ℝ) * ((N : ℝ) * (N + 2))) ^ 2)
    (gaussMat m N 1) ∧ _ at h
  have he : (m : ℝ) * ((N : ℝ) * (N + 2)) = (m : ℝ) * N * (N + 2) := by ring
  rw [he] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp [BstLean.Part36.rhoD, Finset.prod_range_succ]
  ring

end BstLean.Part214
#print axioms BstLean.Part214.gaussian_normSq_pow
#print axioms BstLean.Part214.diagonal_mean
#print axioms BstLean.Part214.diagonal_variance
