import BstLean.Part209GaussianImage
import BstLean.Part209MomentTools
import BstLean.Part167Split

/-! The shared-row transverse moment after the two-input Gaussian decomposition. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153 BstLean.Part134
open BstLean.Part29 (stdGauss)
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part157 (cOf)
open BstLean.Part167 (perp plane_split plane_split_vecMul)

variable {n d p : ℕ}

noncomputable def rowWeights (z : (Fin p → ℝ) × (Fin p → ℝ)) : Fin p → ℝ :=
  fun j => mask (z.1 j) * relu (z.2 j)

lemma measurable_rowWeights : Measurable (rowWeights (p := p)) := by
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_mask.comp ((measurable_pi_apply j).comp measurable_fst)).mul
    (measurable_relu.comp ((measurable_pi_apply j).comp measurable_snd))

lemma rowWeights_le (z : (Fin p → ℝ) × (Fin p → ℝ)) : nrm (rowWeights z) ≤ nrm (reluV z.2) := by
  apply sqrt_le_sqrt
  unfold normSq rowWeights reluV
  apply Finset.sum_le_sum
  intro j _
  unfold mask
  split_ifs <;> simp [sq_nonneg]

noncomputable def rowSum (M : Matrix (Fin p) (Fin d) ℝ) (a b : Fin d → ℝ) : Fin d → ℝ :=
  vecMul (rowWeights (M *ᵥ a, M *ᵥ b)) M

lemma relu_image_lintegral (b : Fin d → ℝ) (v : ℝ) {P : ℕ} (hP : 1 ≤ P) :
    (∫⁻ M : Matrix (Fin p) (Fin d) ℝ, ENNReal.ofReal (nrm (reluV (M *ᵥ b))) ^ (2 * P)
      ∂gaussMat p d v) ≤
      ENNReal.ofReal ((sqrt v * nrm b * (sqrt ((p : ℝ) / 2) + gaussMomConst P)) ^ (2 * P)) := by
  have hF : Measurable (fun z : Fin p → ℝ => ENNReal.ofReal (nrm (reluV z)) ^ (2 * P)) :=
    (BstLean.Part130.measurable_normSq.comp measurable_reluV).sqrt.ennreal_ofReal.pow_const _
  have hM : Measurable (fun M : Matrix (Fin p) (Fin d) ℝ => M *ᵥ b) :=
    (Continuous.matrix_mulVec continuous_id continuous_const).measurable
  rw [← lintegral_map hF hM, gaussMat_mulVec, lintegral_map hF (measurable_const_smul _)]
  change (∫⁻ z, ENNReal.ofReal (nrm (reluV ((sqrt v * nrm b) • z))) ^ (2 * P)
    ∂stdGauss (Fin p)) ≤ _
  have hc := mul_nonneg (sqrt_nonneg v) (nrm_nonneg b)
  simp_rw [reluV_smul_of_nonneg hc, nrm_smul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]
  apply lintegral_pow_const_mul_le hc
  simpa only [ENNReal.ofReal_pow (nrm_nonneg _)] using nrm_reluV_moment_lintegral p hP

lemma image_perp_eq (T : Matrix (Fin n) (Fin d) ℝ) {a : Fin d → ℝ} (ha : T *ᵥ a = 0)
    (z : Fin d → ℝ) : T *ᵥ perp a z = T *ᵥ z := by
  unfold perp
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, smul_zero, sub_zero]

/-- An image that kills both input directions has the sharp transverse moment.
The row weights retain both halfspace gates from the same matrix. -/
theorem transverse_image_lintegral (T : Matrix (Fin n) (Fin d) ℝ) (a b : Fin d → ℝ)
    (ha : T *ᵥ a = 0) (hb : T *ᵥ b = 0) {v : ℝ} (hv : 0 ≤ v) {P : ℕ} (hP : 1 ≤ P) :
    (∫⁻ M : Matrix (Fin p) (Fin d) ℝ, ENNReal.ofReal (nrm (T *ᵥ rowSum M a b)) ^ (2 * P)
      ∂gaussMat p d v) ≤
      ENNReal.ofReal ((v * opN T * nrm b * (sqrt (n : ℝ) + gaussMomConst P) *
        (sqrt ((p : ℝ) / 2) + gaussMomConst P)) ^ (2 * P)) := by
  have hr : T *ᵥ res a b = 0 := by
    unfold res
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, ha, hb, smul_zero, sub_zero]
  let F : (Fin p → ℝ) × (Fin p → ℝ) × (Fin d → ℝ) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (nrm (T *ᵥ z.2.2)) ^ (2 * P)
  have hF : Measurable F :=
    (BstLean.Part130.measurable_normSq.comp (Continuous.matrix_mulVec continuous_const
      continuous_snd.snd).measurable).sqrt.ennreal_ofReal.pow_const _
  have key := plane_split_vecMul v a b measurable_rowWeights hF
  dsimp only [F] at key
  simp only [Matrix.mulVec_add, image_perp_eq T ha, image_perp_eq T hr,
    Matrix.mulVec_smul, ha, hr, smul_zero, zero_add] at key
  change (∫⁻ M, ENNReal.ofReal (nrm (T *ᵥ vecMul (rowWeights (M *ᵥ a, M *ᵥ b)) M)) ^ (2 * P)
    ∂gaussMat p d v) ≤ _
  rw [key]
  let C := sqrt v * (opN T * (sqrt (n : ℝ) + gaussMomConst P))
  have hC : 0 ≤ C := mul_nonneg (sqrt_nonneg _) (mul_nonneg (opN_nonneg _)
    (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _)))
  obtain ⟨hiG, hbG⟩ := gaussian_image_moment T hP
  have hG := lintegral_of_moment (fun z => nrm_nonneg (T *ᵥ z)) hiG hbG
  have hinner : ∀ z : (Fin p → ℝ) × (Fin p → ℝ),
      (∫⁻ γ, ENNReal.ofReal (nrm ((sqrt v * nrm (rowWeights z)) • (T *ᵥ γ))) ^ (2 * P)
        ∂stdGauss (Fin d)) ≤ ENNReal.ofReal (C * nrm (reluV z.2)) ^ (2 * P) := by
    intro z
    have hc := mul_nonneg (sqrt_nonneg v) (nrm_nonneg (rowWeights z))
    simp_rw [nrm_smul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]
    have h := lintegral_pow_const_mul_le hc hG
    refine h.trans ?_
    rw [← ENNReal.ofReal_pow (mul_nonneg hC (nrm_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀
      (mul_nonneg hc (mul_nonneg (opN_nonneg _) (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg _))))
    calc sqrt v * nrm (rowWeights z) * (opN T * (sqrt (n : ℝ) + gaussMomConst P)) =
        C * nrm (rowWeights z) := by dsimp [C]; ring
      _ ≤ C * nrm (reluV z.2) := mul_le_mul_of_nonneg_left (rowWeights_le z) hC
  refine (lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => hinner _).trans ?_
  have hF2 : Measurable (fun z : (Fin p → ℝ) × (Fin p → ℝ) × Matrix (Fin p) (Fin d) ℝ =>
      ENNReal.ofReal (nrm (reluV z.2.1)) ^ (2 * P)) :=
    (BstLean.Part130.measurable_normSq.comp
      (measurable_reluV.comp (measurable_fst.comp measurable_snd))).sqrt.ennreal_ofReal.pow_const _
  have hplane := plane_split v a b hF2
  simp only [lintegral_const, measure_univ, mul_one] at hplane
  simp_rw [ENNReal.ofReal_mul hC, mul_pow,
    lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
  rw [← hplane]
  have h := mul_le_mul' (le_rfl : ENNReal.ofReal C ^ (2 * P) ≤ ENNReal.ofReal C ^ (2 * P))
    (relu_image_lintegral (p := p) b v hP)
  refine h.trans_eq ?_
  rw [← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_mul (pow_nonneg hC _), ← mul_pow]
  apply congrArg ENNReal.ofReal
  simp only [← mul_pow]
  apply congrArg (fun z : ℝ => z ^ (2 * P))
  dsimp [C]
  have hs := mul_self_sqrt hv
  calc sqrt v * (opN T * (sqrt (n : ℝ) + gaussMomConst P)) *
      (sqrt v * nrm b * (sqrt ((p : ℝ) / 2) + gaussMomConst P)) =
      (sqrt v * sqrt v) * opN T * nrm b * (sqrt (n : ℝ) + gaussMomConst P) *
        (sqrt ((p : ℝ) / 2) + gaussMomConst P) := by ring
    _ = _ := by rw [hs]

end BstLean.Part209
