import BstLean.Part200Moments

/-! All-order error moments retain the actual same-weight pair vector. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153

lemma nrm_neg {n : ℕ} (v : Fin n → ℝ) : nrm (-v) = nrm v := by
  unfold nrm normSq
  simp

lemma nrm_sub_le {n : ℕ} (u v : Fin n → ℝ) : nrm (u - v) ≤ nrm u + nrm v := by
  simpa only [sub_eq_add_neg, nrm_neg] using nrm_add_le u (-v)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An integrable vector-length moment controls the error to any fixed ideal vector. -/
theorem error_moment_of_moment {n s : ℕ} {f : Ω → Fin n → ℝ}
    (hf : Measurable f) (hi : Integrable (fun ω => nrm (f ω) ^ s) μ)
    (α : ℝ) (v : Fin n → ℝ) {M : ℝ}
    (hM : (∫ ω, nrm (f ω) ^ s ∂μ) ≤ M) :
    Integrable (fun ω => nrm (α • f ω - v) ^ s) μ ∧
    (∫ ω, nrm (α • f ω - v) ^ s ∂μ) ≤
      2 ^ (s - 1) * (|α| ^ s * M + nrm v ^ s) := by
  have hm : Measurable (fun ω => nrm (α • f ω - v) ^ s) :=
    (BstLean.Part130.measurable_normSq.comp
      ((hf.const_smul α).sub measurable_const)).sqrt.pow_const _
  have hdom : ∀ ω, nrm (α • f ω - v) ^ s ≤
      2 ^ (s - 1) * (|α| ^ s * nrm (f ω) ^ s + nrm v ^ s) := by
    intro ω
    have h := pow_le_pow_left₀ (nrm_nonneg _) (nrm_sub_le (α • f ω) v) s
    rw [nrm_smul] at h
    have h' := add_pow_le (mul_nonneg (abs_nonneg α) (nrm_nonneg (f ω))) (nrm_nonneg v) s
    exact h.trans (by simpa only [mul_pow] using h')
  have hIi : Integrable (fun ω =>
      2 ^ (s - 1) * (|α| ^ s * nrm (f ω) ^ s + nrm v ^ s)) μ :=
    ((hi.const_mul _).add (integrable_const _)).const_mul _
  have hI := hIi.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (pow_nonneg (nrm_nonneg _) _)]; exact hdom ω)
  refine ⟨hI, (integral_mono hI hIi hdom).trans ?_⟩
  rw [integral_const_mul, integral_add (hi.const_mul _) (integrable_const _),
    integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hM (pow_nonneg (abs_nonneg _) _)) le_rfl)
    (by positivity)

variable {n m p : ℕ}

/-- All-order conditional derivative error integrability, including zero features. -/
theorem pairError_conditional_moment {s : ℕ} (hs : 1 ≤ s) {v₂ : ℝ} (hv₂ : 0 ≤ v₂)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) (α : ℝ) (v : Fin n → ℝ) :
    Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ =>
      nrm (α • pairVector A₁ A₂ x x' - v) ^ s) (gaussMat p m v₂) ∧
    (∫ A₂, nrm (α • pairVector A₁ A₂ x x' - v) ^ s ∂gaussMat p m v₂) ≤
      2 ^ (s - 1) * (|α| ^ s *
        (opN A₁ ^ (2 * s) * matrixMoment p m s v₂ * nrm x' ^ s) + nrm v ^ s) := by
  obtain ⟨hi, hb⟩ := pairVector_conditional_moment (p := p) hs hv₂ A₁ hx x'
  have hf : Measurable (fun A₂ : Matrix (Fin p) (Fin m) ℝ => (A₁, A₂)) :=
    measurable_const.prodMk measurable_id
  exact error_moment_of_moment
    ((measurable_pairVector (m := m) (p := p) x x').comp hf) hi α v hb

/-- This bound is a coarse substitute, not the paper's sharp epsilon. -/
theorem pairError_joint_moment {s : ℕ} (hs : 1 ≤ s) {v₁ v₂ : ℝ}
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) (α : ℝ) (v : Fin n → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      nrm (α • pairVector θ.1 θ.2 x x' - v) ^ s)
      ((gaussMat m n v₁).prod (gaussMat p m v₂)) ∧
    (∫ θ, nrm (α • pairVector θ.1 θ.2 x x' - v) ^ s
      ∂((gaussMat m n v₁).prod (gaussMat p m v₂))) ≤
      2 ^ (s - 1) * (|α| ^ s *
        (matrixMoment m n s v₁ * matrixMoment p m s v₂ * nrm x' ^ s) + nrm v ^ s) := by
  obtain ⟨hi, hb⟩ := pairVector_joint_moment (m := m) (p := p) hs hv₁ hv₂ hx x'
  exact error_moment_of_moment (measurable_pairVector x x') hi α v hb

/-- Fubini retains the first-layer conditional distribution of the same error. -/
theorem pairError_fubini {s : ℕ} (hs : 1 ≤ s) {v₁ v₂ : ℝ}
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) (α : ℝ) (v : Fin n → ℝ) :
    (∫ θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ,
      nrm (α • pairVector θ.1 θ.2 x x' - v) ^ s
      ∂((gaussMat m n v₁).prod (gaussMat p m v₂))) =
    ∫ A₁, ∫ A₂, nrm (α • pairVector A₁ A₂ x x' - v) ^ s
      ∂gaussMat p m v₂ ∂gaussMat m n v₁ :=
  integral_prod _ (pairError_joint_moment hs hv₁ hv₂ hx x' α v).1

end BstLean.Part200
