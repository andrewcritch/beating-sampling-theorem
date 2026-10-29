import BstLean.Part209FirstMean
import BstLean.Part209Contraction
import BstLean.Part153PPs2

/-! The radial first-layer term has the sharp transverse moment. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part29 (stdGauss)

variable {n m : ℕ}

lemma transpose_image_lintegral (a : Fin m → ℝ) (v : ℝ) {P : ℕ} (hP : 1 ≤ P) :
    (∫⁻ M : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (nrm (Mᵀ *ᵥ a)) ^ (2 * P)
      ∂gaussMat m n v) ≤
        ENNReal.ofReal ((sqrt v * nrm a * (sqrt (n : ℝ) + gaussMomConst P)) ^ (2 * P)) := by
  have hφ : Measurable (fun z : Fin n → ℝ => ENNReal.ofReal (nrm z) ^ (2 * P)) :=
    BstLean.Part130.measurable_normSq.sqrt.ennreal_ofReal.pow_const _
  have hmv : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => Mᵀ *ᵥ a) :=
    (Continuous.matrix_mulVec continuous_id.matrix_transpose continuous_const).measurable
  rw [← lintegral_map hφ hmv, gaussMat_transpose_mulVec,
    lintegral_map hφ (measurable_const_smul _)]
  change (∫⁻ z, ENNReal.ofReal (nrm ((sqrt v * nrm a) • z)) ^ (2 * P)
    ∂stdGauss (Fin n)) ≤ _
  simp_rw [nrm_smul, abs_of_nonneg (mul_nonneg (sqrt_nonneg _) (nrm_nonneg _)),
    ENNReal.ofReal_mul (mul_nonneg (sqrt_nonneg _) (nrm_nonneg _))]
  apply lintegral_pow_const_mul_le (mul_nonneg (sqrt_nonneg _) (nrm_nonneg _))
  simpa only [ENNReal.ofReal_pow (nrm_nonneg _)] using nrm_moment_lintegral n hP

lemma firstPair_self_eq (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    firstPair A x x = (A * projT x)ᵀ *ᵥ reluV (A *ᵥ x) := by
  unfold firstPair
  rw [firstTangent_eq_tanB]
  unfold tanB
  rw [Matrix.mul_assoc, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, Matrix.diagonal_transpose]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  exact mask_mul_relu _

lemma measurable_firstPair_self (x : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => firstPair A x x) := by
  simp_rw [firstPair_self_eq]
  exact (Continuous.matrix_mulVec
    (continuous_id.matrix_mul continuous_const).matrix_transpose
    (continuous_reluV.comp (continuous_id.matrix_mulVec continuous_const))).measurable

/-- This bound uses the actual first-layer matrix; its tangent and radial coordinates split. -/
theorem firstPair_self_lintegral {x : Fin n → ℝ} (hx : normSq x = 1)
    {v : ℝ} (hv : 0 ≤ v) {P : ℕ} (hP : 1 ≤ P) :
    (∫⁻ A : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (nrm (firstPair A x x)) ^ (2 * P)
      ∂gaussMat m n v) ≤
        ENNReal.ofReal ((v * (sqrt (n : ℝ) + gaussMomConst P) *
          (sqrt ((m : ℝ) / 2) + gaussMomConst P)) ^ (2 * P)) := by
  let Φ : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (nrm (z.2ᵀ *ᵥ reluV z.1)) ^ (2 * P)
  have hΦ : Measurable Φ :=
    ((BstLean.Part130.measurable_normSq.comp (Continuous.matrix_mulVec continuous_snd.matrix_transpose
      (continuous_reluV.comp continuous_fst)).measurable).sqrt.ennreal_ofReal).pow_const _
  simp_rw [firstPair_self_eq]
  change (∫⁻ A, Φ (A *ᵥ x, A * projT x) ∂gaussMat m n v) ≤ _
  rw [gaussMat_decomp hx hv hΦ]
  have hinner : ∀ g : Fin m → ℝ,
      (∫⁻ M, Φ (sqrt v • g, M * projT x) ∂gaussMat m n v) ≤
        ENNReal.ofReal (v * (sqrt (n : ℝ) + gaussMomConst P) * nrm (reluV g)) ^ (2 * P) := by
    intro g
    have hpoint : ∀ M : Matrix (Fin m) (Fin n) ℝ,
        Φ (sqrt v • g, M * projT x) ≤
          ENNReal.ofReal (nrm (Mᵀ *ᵥ reluV (sqrt v • g))) ^ (2 * P) := by
      intro M
      apply pow_le_pow_left'
      apply ENNReal.ofReal_le_ofReal
      change nrm ((M * projT x)ᵀ *ᵥ reluV (sqrt v • g)) ≤ _
      rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, projT_symmetric]
      exact nrm_projT_le hx _
    refine (lintegral_mono hpoint).trans ((transpose_image_lintegral _ v hP).trans_eq ?_)
    rw [reluV_smul_of_nonneg (sqrt_nonneg v), nrm_smul, abs_of_nonneg (sqrt_nonneg v),
      ← ENNReal.ofReal_pow (mul_nonneg
        (mul_nonneg hv (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg P))) (nrm_nonneg _))]
    congr 2
    have hs := mul_self_sqrt hv
    calc sqrt v * (sqrt v * nrm (reluV g)) * (sqrt (n : ℝ) + gaussMomConst P) =
        (sqrt v * sqrt v) * (sqrt (n : ℝ) + gaussMomConst P) * nrm (reluV g) := by ring
      _ = _ := by rw [hs]
  refine (lintegral_mono hinner).trans ?_
  simp_rw [ENNReal.ofReal_mul (mul_nonneg hv (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg P)))]
  apply lintegral_pow_const_mul_le
    (mul_nonneg hv (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg P)))
  simpa only [ENNReal.ofReal_pow (nrm_nonneg _)] using nrm_reluV_moment_lintegral m hP

/-- Integrability follows from the sharp bound, including zero gates. -/
theorem firstPair_self_moment {x : Fin n → ℝ} (hx : normSq x = 1)
    {v : ℝ} (hv : 0 ≤ v) {P : ℕ} (hP : 1 ≤ P) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => nrm (firstPair A x x) ^ (2 * P))
      (gaussMat m n v) ∧
    (∫ A, nrm (firstPair A x x) ^ (2 * P) ∂gaussMat m n v) ≤
      (v * (sqrt (n : ℝ) + gaussMomConst P) *
        (sqrt ((m : ℝ) / 2) + gaussMomConst P)) ^ (2 * P) := by
  have hm : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => nrm (firstPair A x x) ^ (2 * P)) :=
    (BstLean.Part130.measurable_normSq.comp
    (measurable_firstPair_self (m := m) x)).sqrt.pow_const (2 * P)
  have hb := firstPair_self_lintegral (m := m) hx hv hP
  simp_rw [← ENNReal.ofReal_pow (nrm_nonneg _)] at hb
  have hi := (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ fun A => pow_nonneg (nrm_nonneg _) _)).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun A => pow_nonneg (nrm_nonneg _) _)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (pow_nonneg
    (mul_nonneg (mul_nonneg hv (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg P)))
      (add_nonneg (sqrt_nonneg _) (gaussMomConst_nonneg P))) _)).mp hb

noncomputable def pairQ (n P : ℕ) : ℝ :=
  2 / (n : ℝ) ^ 2 * (sqrt (n : ℝ) + gaussMomConst P) *
    ((n : ℝ) / sqrt 2 + gaussMomConst P)

/-- At paper width and variance, the radial error has exactly the allowance `Q_(2P)`. -/
theorem radialPair_moment_paper (hn : 1 ≤ n) {P : ℕ} (hP : 1 ≤ P)
    {x : Fin n → ℝ} (hx : normSq x = 1) :
    Integrable (fun A : Matrix (Fin (n ^ 2)) (Fin n) ℝ =>
      nrm ((n : ℝ)⁻¹ • firstPair A x x) ^ (2 * P)) (gaussMat (n ^ 2) n (2 / n)) ∧
    (∫ A, nrm ((n : ℝ)⁻¹ • firstPair A x x) ^ (2 * P) ∂gaussMat (n ^ 2) n (2 / n)) ≤
      pairQ n P ^ (2 * P) := by
  obtain ⟨hi, hb⟩ := firstPair_self_moment (m := n ^ 2) hx
    (by positivity : 0 ≤ 2 / (n : ℝ)) hP
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp_rw [nrm_smul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹), mul_pow]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (n : ℝ)⁻¹ ^ (2 * P))).trans_eq ?_
  rw [← mul_pow]
  congr 1
  unfold pairQ
  push_cast
  rw [sqrt_div (by positivity), sqrt_sq (by positivity)]
  field_simp
  <;> ring

end BstLean.Part209
