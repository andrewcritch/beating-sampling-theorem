import BstLean.Part200Moments

/-! The conditional pair mean is a Bochner integral with proved integrability. -/
namespace BstLean.Part200
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152 BstLean.Part153

lemma abs_coord_le_nrm {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : |v i| ≤ nrm v := by
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

theorem integrable_vector_of_nrm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n : ℕ} {f : Ω → Fin n → ℝ} (hf : Measurable f)
    (hi : Integrable (fun ω => nrm (f ω)) μ) : Integrable f μ := by
  apply Integrable.of_eval
  intro i
  exact hi.mono' ((measurable_pi_apply i).comp hf).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact abs_coord_le_nrm _ _)

variable {n m p : ℕ}

/-- Every first-layer value has an integrable second-layer pair vector. -/
theorem pairVector_conditional_integrable {v₂ : ℝ} (hv₂ : 0 ≤ v₂)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1)
    (x' : Fin n → ℝ) :
    Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ => pairVector A₁ A₂ x x')
      (gaussMat p m v₂) := by
  have hi : Integrable (fun A₂ : Matrix (Fin p) (Fin m) ℝ =>
      nrm (pairVector A₁ A₂ x x')) (gaussMat p m v₂) := by
    simpa only [pow_one] using
      (pairVector_conditional_moment (p := p) (s := 1) (by omega) hv₂ A₁ hx x').1
  have hf : Measurable (fun A₂ : Matrix (Fin p) (Fin m) ℝ => (A₁, A₂)) :=
    measurable_const.prodMk measurable_id
  have hm : Measurable (fun A₂ : Matrix (Fin p) (Fin m) ℝ => pairVector A₁ A₂ x x') := by
    have h := (measurable_pairVector (m := m) (p := p) x x').comp hf
    simpa only [Function.comp_def] using h
  exact integrable_vector_of_nrm hm hi

theorem pairVector_joint_integrable {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    {x : Fin n → ℝ} (hx : normSq x = 1) (x' : Fin n → ℝ) :
    Integrable (fun θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ =>
      pairVector θ.1 θ.2 x x') ((gaussMat m n v₁).prod (gaussMat p m v₂)) := by
  have hi := (pairVector_joint_moment (m := m) (p := p) (s := 1) (by omega)
    hv₁ hv₂ hx x').1
  simp only [pow_one] at hi
  exact integrable_vector_of_nrm (measurable_pairVector x x') hi

/-- The conditional mean fixes the first layer before integration of the second layer. -/
noncomputable def pairMean (v₂ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) : Fin n → ℝ :=
  ∫ A₂ : Matrix (Fin p) (Fin m) ℝ, pairVector A₁ A₂ x x' ∂gaussMat p m v₂

/-- The iterated vector integral retains the joint distribution of the two layers. -/
theorem pairMean_fubini {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    {x : Fin n → ℝ} (hx : normSq x = 1) (x' : Fin n → ℝ) :
    (∫ θ : Matrix (Fin m) (Fin n) ℝ × Matrix (Fin p) (Fin m) ℝ,
      pairVector θ.1 θ.2 x x' ∂((gaussMat m n v₁).prod (gaussMat p m v₂))) =
    ∫ A₁, pairMean (p := p) v₂ A₁ x x' ∂gaussMat m n v₁ :=
  integral_prod _ (pairVector_joint_integrable hv₁ hv₂ hx x')

theorem pairMean_integrable {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv₂ : 0 ≤ v₂)
    {x : Fin n → ℝ} (hx : normSq x = 1) (x' : Fin n → ℝ) :
    Integrable (fun A₁ : Matrix (Fin m) (Fin n) ℝ => pairMean (p := p) v₂ A₁ x x')
      (gaussMat m n v₁) :=
  (pairVector_joint_integrable (m := m) (p := p) hv₁ hv₂ hx x').integral_prod_left

theorem pairMean_zero_left (v₂ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) (h : reluV (A₁ *ᵥ x) = 0) :
    pairMean (p := p) v₂ A₁ x x' = 0 := by
  simp only [pairMean, pairVector_zero_left A₁ _ x x' h, integral_zero]

theorem pairMean_zero_right (v₂ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (x x' : Fin n → ℝ) (h : reluV (A₁ *ᵥ x') = 0) :
    pairMean (p := p) v₂ A₁ x x' = 0 := by
  simp only [pairMean, pairVector_zero_right A₁ _ x x' h, integral_zero]

end BstLean.Part200
