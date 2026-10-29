import BstLean.Part209Centered

/-! Homogeneity of the shared-row formula and its centered moments. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part151 (mask)

variable {n d p P : ℕ}

lemma kernelVector_zero_right (a : Fin d → ℝ) : kernelVector a 0 = 0 := by
  simp [kernelVector, nrm, normSq]

lemma kernelVector_smul_right (a b : Fin d → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    kernelVector a (c • b) = c • kernelVector a b := by
  by_cases ha : a = 0
  · subst ha; simp [kernelVector_zero_left]
  by_cases hc0 : c = 0
  · subst hc0; simp [kernelVector_zero_right]
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  have hd : dotp a (c • b) = c * dotp a b := by
    unfold dotp
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have he : pairCos a (c • b) = pairCos a b := by
    unfold pairCos
    rw [hd, nrm_smul, abs_of_nonneg hc]
    calc c * dotp a b / (nrm a * (c * nrm b)) =
        c * dotp a b / (c * (nrm a * nrm b)) := by ring
      _ = _ := mul_div_mul_left _ _ hc0
  simp only [kernelVector, if_neg ha, he, nrm_smul, abs_of_nonneg hc,
    smul_add, smul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring

lemma rowSum_smul_right (M : Matrix (Fin p) (Fin d) ℝ) (a b : Fin d → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : rowSum M a (c • b) = c • rowSum M a b := by
  unfold rowSum
  rw [Matrix.mulVec_smul]
  have hw : rowWeights (M *ᵥ a, c • (M *ᵥ b)) = c • rowWeights (M *ᵥ a, M *ᵥ b) := by
    ext j
    simp only [rowWeights, Pi.smul_apply, smul_eq_mul, relu_mul_of_nonneg hc]
    ring
  rw [hw, Matrix.smul_vecMul]

lemma rowSum_zero_right (M : Matrix (Fin p) (Fin d) ℝ) (a : Fin d → ℝ) : rowSum M a 0 = 0 := by
  have hw : rowWeights (M *ᵥ a, (0 : Fin p → ℝ)) = 0 := by
    ext j
    simp [rowWeights, relu]
  rw [rowSum, Matrix.mulVec_zero, hw, Matrix.zero_vecMul]

lemma rowSum_sqrt_scale (M : Matrix (Fin p) (Fin d) ℝ) (a b : Fin d → ℝ)
    {v : ℝ} (hv : 0 ≤ v) : rowSum (sqrt v • M) a b = v • rowSum M a b := by
  by_cases hv0 : v = 0
  · subst hv0; simp [rowSum, rowWeights, relu]
  have hs : 0 < sqrt v := sqrt_pos.mpr (lt_of_le_of_ne hv (Ne.symm hv0))
  unfold rowSum
  rw [Matrix.smul_mulVec, Matrix.smul_mulVec]
  have hw : rowWeights (sqrt v • (M *ᵥ a), sqrt v • (M *ᵥ b)) =
      sqrt v • rowWeights (M *ᵥ a, M *ᵥ b) := by
    ext j
    simp only [rowWeights, Pi.smul_apply, smul_eq_mul, mask_mul_pos hs,
      relu_mul_of_nonneg hs.le]
    ring
  rw [hw, Matrix.smul_vecMul, Matrix.vecMul_smul, smul_smul, mul_self_sqrt hv]

lemma centeredRows_smul_right (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) (a b : Fin d → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : centeredRows n a (c • b) M = c • centeredRows n a b M := by
  simp only [centeredRows, rowSum_smul_right M a b hc, kernelVector_smul_right a b hc,
    smul_sub, smul_smul]
  congr 1
  congr 1
  ring

theorem centeredRows_moment (hn : 1 ≤ n) (hP : 1 ≤ P)
    (T : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d → ℝ) :
    Integrable (fun M => nrm (T *ᵥ centeredRows n a b M) ^ (2 * P)) (gaussMat (n ^ 2) d 1) ∧
    (∫ M, nrm (T *ᵥ centeredRows n a b M) ^ (2 * P) ∂gaussMat (n ^ 2) d 1) ≤
      (opN T * nrm b * (pairTransverse n P + pairPlane n P)) ^ (2 * P) := by
  by_cases hb : b = 0
  · subst hb
    simpa [centeredRows, rowSum_zero_right, kernelVector_zero_right, nrm, normSq,
      show 2 * P ≠ 0 by omega] using
      (integrable_const (0 : ℝ) : Integrable
        (fun _ : Matrix (Fin (n ^ 2)) (Fin d) ℝ => (0 : ℝ)) (gaussMat (n ^ 2) d 1))
  obtain ⟨hi, hm⟩ := centeredRows_unit_moment hn hP T a (normSq_hatV hb)
  have he : nrm b • hatV b = b := by
    rw [hatV, smul_smul, mul_inv_cancel₀ (fun h => hb (nrm_eq_zero' h)), one_smul]
  have hf : ∀ M : Matrix (Fin (n ^ 2)) (Fin d) ℝ,
      nrm (T *ᵥ centeredRows n a b M) = nrm b * nrm (T *ᵥ centeredRows n a (hatV b) M) := by
    intro M
    have h := centeredRows_smul_right M a (hatV b) (nrm_nonneg b)
    rw [he] at h
    rw [h, Matrix.mulVec_smul, nrm_smul, abs_of_nonneg (nrm_nonneg b)]
  obtain ⟨hI, hB⟩ := moment_const_mul (nrm_nonneg b) hi hm
  simp_rw [hf]
  refine ⟨hI, hB.trans_eq ?_⟩
  congr 1
  ring

noncomputable def centeredRowsAt (n : ℕ) (v : ℝ) (a b : Fin d → ℝ)
    (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) : Fin d → ℝ :=
  rowSum M a b - (((n ^ 2 : ℕ) : ℝ) * v / 2) • kernelVector a b

lemma centeredRowsAt_scale (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) (a b : Fin d → ℝ)
    {v : ℝ} (hv : 0 ≤ v) : centeredRowsAt n v a b (sqrt v • M) = v • centeredRows n a b M := by
  simp only [centeredRowsAt, centeredRows, rowSum_sqrt_scale M a b hv, smul_sub, smul_smul]
  congr 1
  congr 1
  ring

theorem centeredRowsAt_moment (hn : 1 ≤ n) (hP : 1 ≤ P)
    (T : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d → ℝ) {v : ℝ} (hv : 0 ≤ v) :
    Integrable (fun M => nrm (T *ᵥ centeredRowsAt n v a b M) ^ (2 * P)) (gaussMat (n ^ 2) d v) ∧
    (∫ M, nrm (T *ᵥ centeredRowsAt n v a b M) ^ (2 * P) ∂gaussMat (n ^ 2) d v) ≤
      (v * opN T * nrm b * (pairTransverse n P + pairPlane n P)) ^ (2 * P) := by
  have hm : Measurable (fun M : Matrix (Fin (n ^ 2)) (Fin d) ℝ =>
      nrm (T *ᵥ centeredRowsAt n v a b M)) :=
    (BstLean.Part130.measurable_normSq.comp ((Continuous.matrix_mulVec continuous_const
      continuous_id).measurable.comp ((measurable_rowSum a b).sub_const _))).sqrt
  obtain ⟨hi, hb⟩ := centeredRows_moment hn hP T a b
  have h := lintegral_of_moment (fun _ => nrm_nonneg _) hi hb
  have hf : ∀ M : Matrix (Fin (n ^ 2)) (Fin d) ℝ,
      nrm (T *ᵥ centeredRowsAt n v a b (sqrt v • M)) = v * nrm (T *ᵥ centeredRows n a b M) := by
    intro M
    rw [centeredRowsAt_scale M a b hv, Matrix.mulVec_smul, nrm_smul, abs_of_nonneg hv]
  apply moment_of_lintegral hm (fun _ => nrm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg hv (opN_nonneg _)) (nrm_nonneg _))
      (add_nonneg (pairTransverse_nonneg _ _) (pairPlane_nonneg _ _)))
  rw [BstLean.Part157.gaussMat_scale, lintegral_map (hm.ennreal_ofReal.pow_const _)
    (measurable_const_smul _)]
  simp_rw [hf, ENNReal.ofReal_mul hv]
  have hh := lintegral_pow_const_mul_le hv h
  convert hh using 1 <;> congr 2 <;> ring

end BstLean.Part209
