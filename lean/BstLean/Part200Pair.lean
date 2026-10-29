import BstLean.Part153SJ
import BstLean.Part153PP
import BstLean.Part153Dec
import BstLean.Part136Kern

/-! The actual fixed-pair tangent vector, including strict zero gates. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153
open BstLean.Part151 (jac mask)

variable {n m p : ℕ}

/-- The paper vector `Π_x J_xᵀ a₂(x')`. Both inputs use the same weights. -/
noncomputable def pairVector (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ) : Fin n → ℝ :=
  (jacT A₁ A₂ x)ᵀ *ᵥ hid2 A₁ A₂ x'

lemma measurable_pair_feature (x' : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      hid2 θ.1 θ.2 x') := by
  have h₁ : Continuous (fun θ : Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin p) (Fin m) ℝ => θ.1 *ᵥ x') :=
    Continuous.matrix_mulVec continuous_fst continuous_const
  have h₂ : Continuous (fun θ : Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin p) (Fin m) ℝ => θ.2 *ᵥ reluV (θ.1 *ᵥ x')) :=
    Continuous.matrix_mulVec continuous_snd (continuous_reluV.comp h₁)
  exact (continuous_reluV.comp h₂).measurable

lemma measurable_pair_jac (x : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin p) (Fin m) ℝ => jacT θ.1 θ.2 x) := by
  have hf : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin p) (Fin m) ℝ => (θ, x)) := measurable_id.prodMk measurable_const
  have h := (measurable_jacT_joint (n := n) (m := m) (m₂ := p)).comp hf
  simpa only [Function.comp_def] using h

lemma measurable_pairVector (x x' : Fin n → ℝ) :
    Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      pairVector θ.1 θ.2 x x') := by
  have hT : Measurable (fun J : Matrix (Fin p) (Fin n) ℝ => Jᵀ) :=
    continuous_id.matrix_transpose.measurable
  have hJ : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin p) (Fin m) ℝ => (jacT θ.1 θ.2 x)ᵀ) :=
    hT.comp (measurable_pair_jac x)
  have hF : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ ×
      Matrix (Fin p) (Fin m) ℝ => ((jacT θ.1 θ.2 x)ᵀ, hid2 θ.1 θ.2 x')) :=
    hJ.prodMk (measurable_pair_feature x')
  exact BstLean.Part134.measurable_mulVec_joint.comp hF

lemma nrm_hid2_le (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x : Fin n → ℝ) :
    nrm (hid2 A₁ A₂ x) ≤ opN A₂ * opN A₁ * nrm x := by
  unfold hid2
  calc nrm (reluV (A₂ *ᵥ reluV (A₁ *ᵥ x)))
      ≤ nrm (A₂ *ᵥ reluV (A₁ *ᵥ x)) := nrm_reluV_le _
    _ ≤ opN A₂ * nrm (reluV (A₁ *ᵥ x)) := nrm_mulVec_le _ _
    _ ≤ opN A₂ * nrm (A₁ *ᵥ x) :=
      mul_le_mul_of_nonneg_left (nrm_reluV_le _) (opN_nonneg _)
    _ ≤ opN A₂ * (opN A₁ * nrm x) :=
      mul_le_mul_of_nonneg_left (nrm_mulVec_le _ _) (opN_nonneg _)
    _ = _ := by ring

/-- A global envelope needs no nonzero gate or length premise. -/
theorem pairVector_le (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) :
    nrm (pairVector A₁ A₂ x x') ≤ opN A₁ ^ 2 * opN A₂ ^ 2 * nrm x' := by
  have hJ : opN (jacT A₁ A₂ x)ᵀ ≤ opN A₂ * opN A₁ := by
    rw [opN_transpose]; exact opN_jacT_le_sj _ _ hx
  calc nrm (pairVector A₁ A₂ x x')
      ≤ opN (jacT A₁ A₂ x)ᵀ * nrm (hid2 A₁ A₂ x') := nrm_mulVec_le _ _
    _ ≤ (opN A₂ * opN A₁) * (opN A₂ * opN A₁ * nrm x') :=
      mul_le_mul hJ (nrm_hid2_le _ _ _) (nrm_nonneg _)
        (mul_nonneg (opN_nonneg _) (opN_nonneg _))
    _ = _ := by ring

/-- A zero first-layer feature at the first input gives the zero strict Jacobian. -/
lemma jac_zero_of_reluV_zero (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x : Fin n → ℝ)
    (h : reluV (A₁ *ᵥ x) = 0) : jac A₁ A₂ x = 0 := by
  ext j l
  simp [jac, h, mask]

/-- A zero first-layer feature at either input gives a zero pair vector. -/
theorem pairVector_zero_left (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ)
    (h : reluV (A₁ *ᵥ x) = 0) : pairVector A₁ A₂ x x' = 0 := by
  simp [pairVector, jacT, jac_zero_of_reluV_zero A₁ A₂ x h]

theorem pairVector_zero_right (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin p) (Fin m) ℝ) (x x' : Fin n → ℝ)
    (h : reluV (A₁ *ᵥ x') = 0) : pairVector A₁ A₂ x x' = 0 := by
  have hH : hid2 A₁ A₂ x' = 0 := by
    ext j
    simp [hid2, h, reluV, relu]
  simp [pairVector, hH]

end BstLean.Part200
