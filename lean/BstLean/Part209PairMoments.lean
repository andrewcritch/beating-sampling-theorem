import BstLean.Part209Scaling
import BstLean.Part209Radial
import BstLean.Part209SharpComplement

/-! The sharp first-layer pair and conditional second-layer fluctuation moments. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part200

variable {n m p P : ℕ}

lemma image_rowSum (T : Matrix (Fin n) (Fin m) ℝ) (M : Matrix (Fin p) (Fin m) ℝ)
    (a b : Fin m → ℝ) (l : Fin n) :
    (T *ᵥ rowSum M a b) l = ∑ j, gatedRow a b (T l) (rowOf j M) := by
  change T l ⬝ᵥ rowSum M a b = _
  rw [dotProduct_comm]
  exact dot_rowSum M a b (T l)

lemma firstPair_rowSum (A : Matrix (Fin m) (Fin n) ℝ) (x x' : Fin n → ℝ) :
    firstPair A x x' = projT x *ᵥ rowSum A x x' := by
  ext l
  rw [firstPair_eq_sum, projT_symmetric, image_rowSum]
  rfl

lemma pairVector_rowSum (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin p) (Fin m) ℝ)
    (x x' : Fin n → ℝ) :
    pairVector A₁ A₂ x x' = firstTangent A₁ x *ᵥ
      rowSum A₂ (reluV (A₁ *ᵥ x)) (reluV (A₁ *ᵥ x')) := by
  ext l
  rw [pairVector_eq_sum, image_rowSum]
  rfl

noncomputable def pairV (n P : ℕ) : ℝ := pairQ n P + 2 * pairPlane n P / (n : ℝ) ^ 2

lemma pairQ_nonneg (n P : ℕ) : 0 ≤ pairQ n P := by
  unfold pairQ
  exact mul_nonneg (mul_nonneg (by positivity)
    (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _)))
    (add_nonneg (by positivity) (gaussMomConst_nonneg _))

lemma pairV_eq (n P : ℕ) :
    pairV n P = 2 / (n : ℝ) ^ 2 * (pairTransverse n P + pairPlane n P) := by
  have hs : sqrt (((n ^ 2 : ℕ) : ℝ) / 2) = (n : ℝ) / sqrt 2 := by
    rw [Nat.cast_pow, sqrt_div (by positivity), sqrt_sq (Nat.cast_nonneg n)]
  unfold pairV pairQ pairTransverse
  rw [hs]
  ring

lemma pairV_nonneg (n P : ℕ) : 0 ≤ pairV n P := by
  rw [pairV_eq]
  apply mul_nonneg (by positivity)
  exact add_nonneg (pairTransverse_nonneg _ _) (pairPlane_nonneg _ _)

noncomputable def firstPairError (x x' : Fin n → ℝ)
    (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) : ℝ :=
  nrm ((n : ℝ)⁻¹ • firstPair A x x' - kernelSlope (dotp x x') • (projT x *ᵥ x'))

lemma firstPairError_eq (hn : 1 ≤ n) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) :
    firstPairError x x' A = (n : ℝ)⁻¹ *
      nrm (projT x *ᵥ centeredRowsAt n (2 / n) x x' A) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have he : (n : ℝ)⁻¹ * (((n ^ 2 : ℕ) : ℝ) * (2 / n) / 2) = 1 := by
    push_cast
    field_simp
  rw [← abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹), ← nrm_smul]
  simp only [centeredRowsAt, Matrix.mulVec_sub, Matrix.mulVec_smul, ← firstPair_rowSum,
    projT_kernelVector hx hx', smul_sub, smul_smul, ← mul_assoc, he, one_mul]
  rfl

lemma measurable_firstPairError (x x' : Fin n → ℝ) : Measurable (firstPairError x x') := by
  unfold firstPairError
  simp_rw [firstPair_rowSum]
  have hm : Measurable (fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ =>
      projT x *ᵥ rowSum A x x') :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp
      (measurable_rowSum x x')
  have he := (hm.const_smul ((n : ℝ)⁻¹)).sub_const
    (kernelSlope (dotp x x') • (projT x *ᵥ x'))
  exact (BstLean.Part130.measurable_normSq.comp he).sqrt

theorem firstPairError_moment (hn : 1 ≤ n) (hP : 1 ≤ P) {x x' : Fin n → ℝ}
    (hx : normSq x = 1) (hx' : normSq x' = 1) :
    Integrable (fun A => firstPairError x x' A ^ (2 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, firstPairError x x' A ^ (2 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤ pairV n P ^ (2 * P) := by
  obtain ⟨hi, hb⟩ := centeredRowsAt_moment hn hP (projT x) x x' (by positivity : 0 ≤ 2 / (n : ℝ))
  obtain ⟨hI, hB⟩ := moment_const_mul (by positivity : 0 ≤ (n : ℝ)⁻¹) hi hb
  simp_rw [← firstPairError_eq hn hx hx'] at hI hB
  refine ⟨hI, hB.trans ?_⟩
  have hq : 0 ≤ pairTransverse n P + pairPlane n P :=
    add_nonneg (pairTransverse_nonneg _ _) (pairPlane_nonneg _ _)
  have hop := opN_nonneg (projT x)
  have hnr := nrm_nonneg x'
  apply pow_le_pow_left₀ (by positivity)
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnrm : nrm x' = 1 := by simp only [nrm, hx', sqrt_one]
  rw [hnrm, mul_one, pairV_eq]
  have h := mul_le_mul_of_nonneg_right (opN_projT_le hx) hq
  have hc := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 / (n : ℝ) ^ 2)
  convert hc using 1 <;> field_simp <;> ring

noncomputable def fluctuation (x x' : Fin n → ℝ)
    (A₁ : Matrix (Fin (n ^ 2)) (Fin n) ℝ) (A₂ : Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ) : ℝ :=
  nrm ((n : ℝ)⁻¹ • (pairVector A₁ A₂ x x' - pairMean (p := n ^ 2) (2 / (n ^ 2 : ℕ)) A₁ x x'))

theorem fluctuation_conditional_moment (hn : 1 ≤ n) (hP : 1 ≤ P)
    (x x' : Fin n → ℝ) (A : Matrix (Fin (n ^ 2)) (Fin n) ℝ) :
    Integrable (fun B => fluctuation x x' A B ^ (2 * P)) (gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ))) ∧
    (∫ B, fluctuation x x' A B ^ (2 * P) ∂gaussMat (n ^ 2) (n ^ 2) (2 / (n ^ 2 : ℕ))) ≤
      (pairV n P * (opN (firstTangent A x) / sqrt (n : ℝ)) * layerLength A x') ^ (2 * P) := by
  obtain ⟨hi, hb⟩ := centeredRowsAt_moment hn hP (firstTangent A x)
    (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) (by positivity : 0 ≤ 2 / ((n ^ 2 : ℕ) : ℝ))
  have he : ∀ B : Matrix (Fin (n ^ 2)) (Fin (n ^ 2)) ℝ,
      fluctuation x x' A B = (n : ℝ)⁻¹ * nrm (firstTangent A x *ᵥ
        centeredRowsAt n (2 / (n ^ 2 : ℕ)) (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) B) := by
    intro B
    rw [fluctuation, nrm_smul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹),
      pairVector_rowSum, pairMean_closed (by positivity), centeredRowsAt,
      Matrix.mulVec_sub, Matrix.mulVec_smul]
  obtain ⟨hI, hB⟩ := moment_const_mul (by positivity : 0 ≤ (n : ℝ)⁻¹) hi hb
  simp_rw [← he] at hI hB
  refine ⟨hI, hB.trans_eq ?_⟩
  congr 1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pairV_eq, layerLength_eq hn]
  push_cast
  field_simp
  rw [sq_sqrt hn0.le]
  ring

end BstLean.Part209
