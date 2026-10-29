import BstLean.Part205Covariance

/-! Match the finite covariance sum to the paper's matrix trace and quadratic form. -/
namespace BstLean.Part205
open MeasureTheory ProbabilityTheory
open BstLean.Part130 BstLean.Part139

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable {m : ℕ} (g : Ω → Fin m → ℝ)

noncomputable def covarianceMatrix : Matrix (Fin m) (Fin m) ℝ := fun i j => covV μ g i j

lemma covariance_symmetry (i j : Fin m) : covV μ g i j = covV μ g j i := by
  unfold covV
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

theorem covarianceT_matrix (Q : ℝ) : covarianceT μ g Q =
    ((covarianceMatrix μ g ^ 2).trace +
      2 * dotp (meanV μ g) ((covarianceMatrix μ g).mulVec (meanV μ g))) / Q ^ 2 := by
  have htr : (covarianceMatrix μ g ^ 2).trace = ∑ i, ∑ j, covV μ g i j ^ 2 := by
    rw [pow_two]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, covarianceMatrix]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [covariance_symmetry μ g j i, pow_two]
  have hq : dotp (meanV μ g) ((covarianceMatrix μ g).mulVec (meanV μ g)) =
      ∑ i, ∑ j, meanV μ g i * covV μ g i j * meanV μ g j := by
    unfold dotp Matrix.mulVec dotProduct covarianceMatrix
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [htr, hq]
  rfl

end
end BstLean.Part205

#print axioms BstLean.Part205.covarianceT_matrix
