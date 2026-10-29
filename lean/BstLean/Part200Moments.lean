import BstLean.Part200Pair

/-! Conditional and joint moments of the actual pair vector. The bounds are coarse. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153

variable {n m p : ℕ}

/-- The existing Gaussian operator moment constant at order `2s`. -/
noncomputable def matrixMoment (a b s : ℕ) (v : ℝ) : ℝ :=
  (√v * (√a + √b + gaussMomConst s)) ^ (2 * s)

lemma matrixMoment_nonneg (a b s : ℕ) (v : ℝ) : 0 ≤ matrixMoment a b s v := by
  unfold matrixMoment
  exact pow_nonneg (mul_nonneg (sqrt_nonneg _)
    (add_nonneg (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (gaussMomConst_nonneg _))) _

/-- The integrable envelope for the pair moment under the actual product of weights. -/
theorem pair_envelope_moment {s : ℕ} (hs : 1 ≤ s) {v₁ v₂ : ℝ}
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) (x' : Fin n → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      opN θ.1 ^ (2 * s) * opN θ.2 ^ (2 * s) * nrm x' ^ s)
      ((gaussMat m n v₁).prod (gaussMat p m v₂)) ∧
    (∫ θ, opN θ.1 ^ (2 * s) * opN θ.2 ^ (2 * s) * nrm x' ^ s
      ∂((gaussMat m n v₁).prod (gaussMat p m v₂))) ≤
      matrixMoment m n s v₁ * matrixMoment p m s v₂ * nrm x' ^ s := by
  obtain ⟨hi₁, hb₁⟩ := opN_moment (p := m) (q := n) hv₁ hs
  obtain ⟨hi₂, hb₂⟩ := opN_moment (p := p) (q := m) hv₂ hs
  refine ⟨(hi₁.mul_prod hi₂).mul_const _, ?_⟩
  rw [integral_mul_const, integral_prod_mul
    (fun A₁ : Matrix (Fin m) (Fin n) ℝ => opN A₁ ^ (2 * s))
    (fun A₂ : Matrix (Fin p) (Fin m) ℝ => opN A₂ ^ (2 * s))]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hb₁ hb₂ (integral_nonneg fun M => pow_nonneg (opN_nonneg M) _)
      (matrixMoment_nonneg _ _ _ _)) (pow_nonneg (nrm_nonneg _) _)

/-- All positive integer pair moments are integrable for every fixed first layer.
The second layer uses the same rows at the two inputs. -/
theorem pairVector_conditional_moment {s : ℕ} (hs : 1 ≤ s) {v : ℝ} (hv : 0 ≤ v)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) :
    Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ =>
      nrm (pairVector A₁ A₂ x x') ^ s) (gaussMat p m v) ∧
    (∫ A₂, nrm (pairVector A₁ A₂ x x') ^ s ∂gaussMat p m v) ≤
      opN A₁ ^ (2 * s) * matrixMoment p m s v * nrm x' ^ s := by
  obtain ⟨hi, hb⟩ := opN_moment (p := p) (q := m) hv hs
  have hf : Measurable (fun A₂ : Matrix (Fin p) (Fin m) ℝ => (A₁, A₂)) :=
    measurable_const.prodMk measurable_id
  have hm := (measurable_pairVector (m := m) (p := p) x x').comp hf
  have hNm : Measurable (fun A₂ : Matrix (Fin p) (Fin m) ℝ =>
      nrm (pairVector A₁ A₂ x x') ^ s) :=
    (BstLean.Part130.measurable_normSq.comp hm).sqrt.pow_const _
  have hdom : ∀ A₂ : Matrix (Fin p) (Fin m) ℝ,
      nrm (pairVector A₁ A₂ x x') ^ s ≤
        opN A₁ ^ (2 * s) * opN A₂ ^ (2 * s) * nrm x' ^ s := by
    intro A₂
    have h := pow_le_pow_left₀ (nrm_nonneg _) (pairVector_le A₁ A₂ hx x') s
    simpa only [mul_pow, ← pow_mul] using h
  have hIi := (hi.const_mul (opN A₁ ^ (2 * s))).mul_const (nrm x' ^ s)
  have hI : Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ =>
      nrm (pairVector A₁ A₂ x x') ^ s) (gaussMat p m v) :=
    hIi.mono' hNm.aestronglyMeasurable (ae_of_all _ fun A₂ => by
      rw [Real.norm_of_nonneg (pow_nonneg (nrm_nonneg _) _)]; exact hdom A₂)
  refine ⟨hI, (integral_mono hI hIi hdom).trans ?_⟩
  rw [integral_mul_const, integral_const_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (pow_nonneg (opN_nonneg _) _))
    (pow_nonneg (nrm_nonneg _) _)

/-- All positive integer moments use the actual joint distribution of both layers. -/
theorem pairVector_joint_moment {s : ℕ} (hs : 1 ≤ s) {v₁ v₂ : ℝ}
    (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      nrm (pairVector θ.1 θ.2 x x') ^ s)
      ((gaussMat m n v₁).prod (gaussMat p m v₂)) ∧
    (∫ θ, nrm (pairVector θ.1 θ.2 x x') ^ s
      ∂((gaussMat m n v₁).prod (gaussMat p m v₂))) ≤
      matrixMoment m n s v₁ * matrixMoment p m s v₂ * nrm x' ^ s := by
  obtain ⟨hi, hb⟩ := pair_envelope_moment (m := m) (p := p) hs hv₁ hv₂ x'
  have hm : Measurable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      nrm (pairVector θ.1 θ.2 x x') ^ s) :=
    (BstLean.Part130.measurable_normSq.comp (measurable_pairVector x x')).sqrt.pow_const _
  have hdom : ∀ θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ,
      nrm (pairVector θ.1 θ.2 x x') ^ s ≤
        opN θ.1 ^ (2 * s) * opN θ.2 ^ (2 * s) * nrm x' ^ s := by
    intro θ
    have h := pow_le_pow_left₀ (nrm_nonneg _) (pairVector_le θ.1 θ.2 hx x') s
    simpa only [mul_pow, ← pow_mul] using h
  have hI := hi.mono' hm.aestronglyMeasurable (ae_of_all _ fun θ => by
    rw [Real.norm_of_nonneg (pow_nonneg (nrm_nonneg _) _)]; exact hdom θ)
  exact ⟨hI, (integral_mono hI hi hdom).trans hb⟩

end BstLean.Part200
