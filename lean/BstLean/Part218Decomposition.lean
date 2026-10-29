import BstLean.Part218ConcreteKernels
import BstLean.Part218Frobenius

/-! Diagonal and off-diagonal splits of the actual covariance and input norm statistics. -/
namespace BstLean.Part218
open MeasureTheory Real
open BstLean.Part29 BstLean.Part105 BstLean.Part130 BstLean.Part132 BstLean.Part133
open BstLean.Part137 BstLean.Part214

lemma dotp_self {N : ℕ} (x : Fin N → ℝ) : dotp x x = normSq x := by
  simp only [dotp, normSq, pow_two]

lemma kernelPhi_self {N : ℕ} (x : Fin N → ℝ) : kernelPhi x x = normSq x := by
  by_cases hx : normSq x = 0
  · have hzero := normSq_eq_zero hx
    subst x
    simp [kernelPhi, nrm, normSq, dotp]
  · change nrm x * nrm x * BstLean.Part130.kappa (dotp x x / (nrm x * nrm x)) = normSq x
    rw [← pow_two, nrm_sq, dotp_self, div_self hx, kappa_one, mul_one]

lemma remainder_diagonal {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) (i : Fin m) :
    firstRemainderEntry M i i = (1 / (4 * (N : ℝ)) - cN N ^ 2) * normSq (rowOf i M) := by
  unfold firstRemainderEntry firstLinearEntry
  rw [firstCovEntry_formula hN, kernelPhi_self, dotp_self]
  have he : cN N ^ 2 * nrm (rowOf i M) * nrm (rowOf i M) = cN N ^ 2 * normSq (rowOf i M) := by
    rw [mul_assoc, ← pow_two, nrm_sq]
  rw [he]
  ring

lemma remainder_square {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) (i j : Fin m) :
    firstRemainderEntry M i j ^ 2 = remainderKernel N (rowOf i M, rowOf j M) := by
  rw [firstRemainderEntry_formula hN]
  unfold remainderKernel
  rw [mul_pow, mul_pow, nrm_sq, nrm_sq]

lemma reluSquarePair_one : reluSquarePair 1 = 3 / 2 := by
  unfold reluSquarePair
  simp only [sC, one_pow, sub_self, sqrt_zero, one_smul, zero_smul, add_zero, ← pow_add]
  have he := integral_fun_fst (μ := stdGauss (Fin 1)) (ν := stdGauss (Fin 1))
    (fun x : Fin 1 → ℝ => relu (x 0) ^ 4)
  simp only [probReal_univ, one_smul] at he
  exact he.trans ((gaussian_coordinate_integral (ι := Fin 1) 0
    (measurable_relu.pow_const 4)).trans int_relu_four)

noncomputable def normDiagonal (N : ℕ) : ℝ :=
  3 / (2 * (N : ℝ) * (N + 2)) - 1 / (4 * (N : ℝ) ^ 2)

lemma normKernel_diagonal {N : ℕ} (hN : 1 ≤ N) (x : Fin N → ℝ) :
    normKernel N (x, x) = normDiagonal N * normSq x ^ 2 := by
  rw [normKernel_formula hN]
  by_cases hx : normSq x = 0
  · simp [hx]
  have hc : rowCos x x = 1 := by
    unfold rowCos
    rw [dotp_self, ← pow_two, nrm_sq, div_self hx]
  rw [hc]
  unfold squaredAngularB normDiagonal
  rw [reluSquarePair_one]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp

lemma offStatistic_split {N m : ℕ} (φ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (M : Matrix (Fin m) (Fin N) ℝ) :
    (∑ i, ∑ j, φ (rowOf i M, rowOf j M)) =
      (∑ i, φ (rowOf i M, rowOf i M)) + offStatistic φ m M := by
  classical
  have he : ∀ p : Fin m × Fin m, orderedRow φ p M =
      φ (M p.1, M p.2) - if p.1 = p.2 then φ (M p.1, M p.1) else 0 := by
    intro p
    by_cases hp : p.1 = p.2 <;> simp [orderedRow, hp]
  unfold offStatistic
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (∑ i, ∑ j, φ (M i, M j)) =
    (∑ i, φ (M i, M i)) + ((∑ i, ∑ j, φ (M i, M j)) - ∑ i, φ (M i, M i))
  ring

theorem remainderFrob_split {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    remainderFrobSq M = (1 / (4 * (N : ℝ)) - cN N ^ 2) ^ 2 * diagonalSum N m M +
      offStatistic (remainderKernel N) m M := by
  unfold remainderFrobSq
  simp_rw [remainder_square hN]
  rw [offStatistic_split]
  congr 1
  unfold diagonalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← remainder_square hN, remainder_diagonal hN, mul_pow]

end BstLean.Part218
#print axioms BstLean.Part218.remainderFrob_split
#print axioms BstLean.Part218.normKernel_diagonal
