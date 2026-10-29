import BstLean.Part209PlaneGeometry
import BstLean.Part209PlaneCoordinates
import BstLean.Part209MomentMore

/-! Centered shared-row moments at unit entry variance. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part134

variable {n d p P : ℕ}

lemma measurable_rowSum (a b : Fin d → ℝ) :
    Measurable (fun M : Matrix (Fin p) (Fin d) ℝ => rowSum M a b) := by
  exact (Continuous.matrix_vecMul continuous_fst continuous_snd).measurable.comp
    ((measurable_rowWeights.comp
      ((Continuous.matrix_mulVec continuous_id continuous_const).measurable.prodMk
        (Continuous.matrix_mulVec continuous_id continuous_const).measurable)).prodMk measurable_id)

lemma dot_rowSum (M : Matrix (Fin p) (Fin d) ℝ) (a b u : Fin d → ℝ) :
    dotp (rowSum M a b) u = ∑ j, gatedRow a b u (rowOf j M) := by
  unfold dotp rowSum vecMul dotProduct rowWeights gatedRow
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i, BstLean.Part151.mask ((M *ᵥ a) j) * relu ((M *ᵥ b) j) *
    M j i * u i) = _
  simp only [rowOf, Matrix.mulVec, dotProduct, dotp]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

noncomputable def centeredRows (n : ℕ) (a b : Fin d → ℝ)
    (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) : Fin d → ℝ :=
  rowSum M a b - (((n ^ 2 : ℕ) : ℝ) / 2) • kernelVector a b

lemma measurable_centeredRows (a b : Fin d → ℝ) : Measurable (centeredRows n a b) :=
  (measurable_rowSum a b).sub_const _

lemma dot_centeredRows (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) (a b u : Fin d → ℝ) :
    dotp (centeredRows n a b M) u = coordinateError n a b u M := by
  have he : ∀ z k : Fin d → ℝ, ∀ c : ℝ, dotp (z - c • k) u = dotp z u - c * dotp k u := by
    intros
    simp only [dotp, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
      Finset.sum_sub_distrib, mul_assoc, Finset.mul_sum]
  rw [centeredRows, he, dot_rowSum]
  rfl

lemma centeredRows_plane (M : Matrix (Fin (n ^ 2)) (Fin d) ℝ) (a b : Fin d → ℝ) :
    planePart a b (centeredRows n a b M) =
      coordinateError n a b (hatV a) M • hatV a +
        coordinateError n a b (hatV (res a b)) M • hatV (res a b) := by
  simp only [planePart, dot_centeredRows]

noncomputable def pairTransverse (n P : ℕ) : ℝ :=
  (sqrt (n : ℝ) + gaussMomConst P) * (sqrt (((n ^ 2 : ℕ) : ℝ) / 2) + gaussMomConst P)

lemma pairTransverse_nonneg (n P : ℕ) : 0 ≤ pairTransverse n P := by
  unfold pairTransverse
  exact mul_nonneg (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _))
    (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _))

lemma pairPlane_nonneg (n P : ℕ) : 0 ≤ pairPlane n P := by
  unfold pairPlane factorialRoot
  have hlog : 0 ≤ log (162 : ℝ) := zero_le_one.trans one_le_log162
  positivity

theorem centeredRows_unit_moment (hn : 1 ≤ n) (hP : 1 ≤ P)
    (T : Matrix (Fin n) (Fin d) ℝ) (a : Fin d → ℝ) {b : Fin d → ℝ} (hb : normSq b = 1) :
    Integrable (fun M => nrm (T *ᵥ centeredRows n a b M) ^ (2 * P)) (gaussMat (n ^ 2) d 1) ∧
    (∫ M, nrm (T *ᵥ centeredRows n a b M) ^ (2 * P) ∂gaussMat (n ^ 2) d 1) ≤
      (opN T * (pairTransverse n P + pairPlane n P)) ^ (2 * P) := by
  let R := offPlane a b
  let TR := T * R
  have hTRa : TR *ᵥ a = 0 := by
    rw [show TR = T * offPlane a b from rfl, ← Matrix.mulVec_mulVec, (offPlane_kills a b).1]
    simp
  have hTRb : TR *ᵥ b = 0 := by
    rw [show TR = T * offPlane a b from rfl, ← Matrix.mulVec_mulVec, (offPlane_kills a b).2]
    simp
  have ht := transverse_image_lintegral (p := n ^ 2) TR a b hTRa hTRb
    (by norm_num : (0 : ℝ) ≤ 1) hP
  have hbN : nrm b = 1 := by simp only [nrm, hb, sqrt_one]
  simp only [one_mul, hbN, mul_one] at ht
  have htm : Measurable (fun M : Matrix (Fin (n ^ 2)) (Fin d) ℝ => nrm (TR *ᵥ rowSum M a b)) :=
    (BstLean.Part130.measurable_normSq.comp ((Continuous.matrix_mulVec continuous_const
      continuous_id).measurable.comp (measurable_rowSum a b))).sqrt
  have hc : 0 ≤ opN T * pairTransverse n P := mul_nonneg (opN_nonneg _) (pairTransverse_nonneg _ _)
  have htb : (opN TR * (sqrt (n : ℝ) + gaussMomConst P) *
      (sqrt (((n ^ 2 : ℕ) : ℝ) / 2) + gaussMomConst P)) ^ (2 * P) ≤
      (opN T * pairTransverse n P) ^ (2 * P) := by
    rw [mul_assoc]
    exact pow_le_pow_left₀ (mul_nonneg (opN_nonneg _) (pairTransverse_nonneg _ _))
      (mul_le_mul_of_nonneg_right (offPlane_contract a b T) (pairTransverse_nonneg _ _)) _
  obtain ⟨hiT, hbT⟩ := moment_of_lintegral htm (fun _ => nrm_nonneg _) hc
    (ht.trans (ENNReal.ofReal_le_ofReal htb))
  obtain ⟨hiP, hbP⟩ := coordinatePlane_moment hn hP a hb (hatV_zero_or_unit a)
    (hatV_zero_or_unit (res a b))
  simp_rw [← centeredRows_plane] at hiP hbP
  obtain ⟨hiS, hbS⟩ := moment_const_mul (opN_nonneg T) hiP hbP
  have hmP : Measurable (fun M : Matrix (Fin (n ^ 2)) (Fin d) ℝ =>
      nrm (planePart a b (centeredRows n a b M))) := by
    simp only [centeredRows_plane]
    exact (BstLean.Part130.measurable_normSq.comp
      (((measurable_coordinateError a b (hatV a)).smul_const _).add
        ((measurable_coordinateError a b (hatV (res a b))).smul_const _))).sqrt
  have hpp : 0 ≤ pairPlane n P := pairPlane_nonneg n P
  obtain ⟨hi, hh⟩ := moment_add htm (hmP.const_mul (opN T)) (fun _ => nrm_nonneg _)
    (fun _ => mul_nonneg (opN_nonneg _) (nrm_nonneg _)) (by omega : 1 ≤ 2 * P)
    hc (mul_nonneg (opN_nonneg _) hpp) hiT hiS hbT hbS
  have hm : Measurable (fun M : Matrix (Fin (n ^ 2)) (Fin d) ℝ =>
      nrm (T *ᵥ centeredRows n a b M)) :=
    (BstLean.Part130.measurable_normSq.comp ((Continuous.matrix_mulVec continuous_const
      continuous_id).measurable.comp (measurable_centeredRows a b))).sqrt
  have hdom : ∀ M, nrm (T *ᵥ centeredRows n a b M) ≤
      nrm (TR *ᵥ rowSum M a b) + opN T * nrm (planePart a b (centeredRows n a b M)) := by
    intro M
    have he := plane_decomposition a b (centeredRows n a b M)
    have hr : R *ᵥ centeredRows n a b M = R *ᵥ rowSum M a b := by
      rw [centeredRows, Matrix.mulVec_sub, Matrix.mulVec_smul]
      rw [show R *ᵥ kernelVector a b = 0 from offPlane_kernel a b, smul_zero, sub_zero]
    have h := nrm_add_le (T *ᵥ planePart a b (centeredRows n a b M))
      (T *ᵥ (R *ᵥ centeredRows n a b M))
    rw [← Matrix.mulVec_add, he, hr, Matrix.mulVec_mulVec] at h
    exact h.trans (by linarith [nrm_mulVec_le T (planePart a b (centeredRows n a b M))])
  obtain ⟨hI, hB⟩ := moment_mono hm (fun _ => nrm_nonneg _) hdom hi hh
  refine ⟨hI, hB.trans_eq ?_⟩
  congr 1
  ring

end BstLean.Part209
