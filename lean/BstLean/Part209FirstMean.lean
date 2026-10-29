import BstLean.Part209Mean

/-! Exact first-layer tangent means under shared Gaussian weights. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200
open BstLean.Part151 (mask maskedF)

variable {n m : ℕ}

noncomputable def firstPair (A : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) : Fin n → ℝ :=
  firstTangent A x *ᵥ reluV (A *ᵥ x')

lemma firstPair_eq_sum (A : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) (l : Fin n) :
    firstPair A x x' l = ∑ j, mask ((A *ᵥ x) j) * (A *ᵥ (projT x)ᵀ l) j * relu ((A *ᵥ x') j) := by
  simp only [firstPair, firstTangent, maskedF, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply, reluV]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

theorem firstPair_integrable {v : ℝ} (hv : 0 ≤ v) (x x' : Fin n → ℝ) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => firstPair A x x') (gaussMat m n v) := by
  apply Integrable.of_eval
  intro l
  simp only [firstPair_eq_sum]
  exact integrable_finsetSum _ fun j _ => matrix_row_integrable hv x x' _ j

lemma projT_symmetric (x : Fin n → ℝ) : (projT x)ᵀ = projT x := by
  ext i j
  simp only [projT, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  congr 1
  · simp [eq_comm]
  · ring

theorem firstPair_mean {v : ℝ} (hv : 0 ≤ v) (x x' : Fin n → ℝ) :
    (∫ A : Matrix (Fin m) (Fin n) ℝ, firstPair A x x' ∂gaussMat m n v) =
      ((m : ℝ) * v / 2) • (projT x *ᵥ kernelVector x x') := by
  funext l
  have hi := firstPair_integrable (m := m) hv x x'
  have he := (ContinuousLinearMap.proj l : (Fin n → ℝ) →L[ℝ] ℝ).integral_comp_comm hi
  change (∫ A : Matrix (Fin m) (Fin n) ℝ, firstPair A x x' l ∂gaussMat m n v) =
    (∫ A, firstPair A x x' ∂gaussMat m n v) l at he
  rw [← he]
  simp_rw [firstPair_eq_sum]
  rw [matrix_pair_mean hv, projT_symmetric]
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, dotp]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma projT_self_zero {x : Fin n → ℝ} (hx : normSq x = 1) : projT x *ᵥ x = 0 := by
  rw [projT_mulVec]
  have hd : x ⬝ᵥ x = 1 := by simpa only [normSq, dotProduct, ← sq] using hx
  rw [hd, one_smul, sub_self]

lemma projT_kernelVector {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) :
    projT x *ᵥ kernelVector x x' = kernelSlope (dotp x x') • (projT x *ᵥ x') := by
  have hx0 : x ≠ 0 := by intro h; simp [h, normSq] at hx
  have hc : pairCos x x' = dotp x x' := by simp [pairCos, nrm, hx, hx']
  rw [kernelVector, if_neg hx0, hc, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, projT_self_zero hx, smul_zero, add_zero]

/-- The normalized first-layer derivative has the exact ideal single-kernel mean. -/
theorem firstPair_mean_paper {n : ℕ} (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    (∫ A : Matrix (Fin (n ^ 2)) (Fin n) ℝ, (n : ℝ)⁻¹ • firstPair A x x'
      ∂gaussMat (n ^ 2) n (2 / n)) = kernelSlope (dotp x x') • (projT x *ᵥ x') := by
  rw [integral_smul, firstPair_mean (by positivity), projT_kernelVector hx hx', smul_smul]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he : (n : ℝ)⁻¹ * ((n ^ 2 : ℕ) * (2 / (n : ℝ)) / 2) = 1 := by
    push_cast
    field_simp
  rw [he, one_smul]

/-- The radial first-layer tangent vector has mean zero. -/
theorem firstPair_self_mean {v : ℝ} (hv : 0 ≤ v) {x : Fin n → ℝ} (hx : normSq x = 1) :
    (∫ A : Matrix (Fin m) (Fin n) ℝ, firstPair A x x ∂gaussMat m n v) = 0 := by
  rw [firstPair_mean hv, projT_kernelVector hx hx, projT_self_zero hx, smul_zero, smul_zero]

end BstLean.Part209
