import BstLean.Part132Layer

/-!
# Part 132, item 3 (tools): a lower bound of the kernel through a whole network

Role: `delegations/statements/p132-spec.md`. Paper source: `onW4c-cx.md` §3 ("F_2 and F_3, then
F_1", "A_3", "A_2, then A_1"); `onW4-opus-prover.md` 2.1 to 2.3.

* `integral_prod_ge`, `integral_prod_le`: Fubini with a bound of the inner integral.
* `integral_drop3`, `integrable_drop3`: a function of the first two of three independent
  coordinates.
* `sqrt_pair_le`: `E √X√Y ≤ αβ` if `E X = α²`, `E Y = β²` (Cauchy–Schwarz).
* `hid2_sq`, `hid2_four`: the second and fourth moment of the last hidden vector.
* `hid2_dot_lower`: `E ⟨h₂(y), h₂(y′)⟩ ≥ (m₂/2)v₂(m₁/2)v₁·[Ψ_{κ∘κ}(y, y′) − (10/m₁)κ(0)|y||y′|]`.
* `mlp_psi_lower`: for a random ReLU MLP `N : ℝ^k → ℝ^q` with hidden width `m`:
  `E Ψ_G(N(z), N(z′)) ≥ (2q/k)·[Ψ_{G∘κ∘κ}(z, z′) − ((4/q)G(0) + 20/m)|z||z′|]`.
* `mlp_nrm_upper`: `E |N(z)||N(z′)| ≤ (2q/k)|z||z′|`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130

/-! ## Fubini helpers -/

section fubini

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {τ : Measure γ} [SFinite μ] [SFinite ν]

lemma integral_prod_ge {f : α × β → ℝ} (hf : Integrable f (μ.prod ν)) {g : α → ℝ}
    (hg : Integrable g μ) (h : ∀ x, g x ≤ ∫ y, f (x, y) ∂ν) :
    ∫ x, g x ∂μ ≤ ∫ z, f z ∂(μ.prod ν) := by
  rw [integral_prod _ hf]
  exact integral_mono hg hf.integral_prod_left h

lemma integral_prod_le {f : α × β → ℝ} (hf : Integrable f (μ.prod ν)) {g : α → ℝ}
    (hg : Integrable g μ) (h : ∀ x, ∫ y, f (x, y) ∂ν ≤ g x) :
    ∫ z, f z ∂(μ.prod ν) ≤ ∫ x, g x ∂μ := by
  rw [integral_prod _ hf]
  exact integral_mono hf.integral_prod_left hg h

lemma map_drop3 [IsProbabilityMeasure τ] :
    (μ.prod (ν.prod τ)).map (fun θ : α × β × γ => (θ.1, θ.2.1)) = μ.prod ν := by
  have h := Measure.map_prod_map μ (ν.prod τ) (f := id) (g := Prod.fst) measurable_id
    measurable_fst
  rw [Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] at h
  rw [h]
  rfl

lemma integral_drop3 [IsProbabilityMeasure τ] {f : α × β → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∫ θ : α × β × γ, f (θ.1, θ.2.1) ∂(μ.prod (ν.prod τ)) = ∫ z, f z ∂(μ.prod ν) := by
  have hm : Measurable (fun θ : α × β × γ => (θ.1, θ.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have h := integral_map (μ := μ.prod (ν.prod τ)) hm.aemeasurable (f := f)
    (by rw [map_drop3]; exact hf)
  rw [map_drop3] at h
  exact h.symm

lemma integrable_drop3 [IsProbabilityMeasure τ] {f : α × β → ℝ}
    (hf : Integrable f (μ.prod ν)) :
    Integrable (fun θ : α × β × γ => f (θ.1, θ.2.1)) (μ.prod (ν.prod τ)) := by
  have hm : Measurable (fun θ : α × β × γ => (θ.1, θ.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have h : Integrable f ((μ.prod (ν.prod τ)).map (fun θ : α × β × γ => (θ.1, θ.2.1))) := by
    rw [map_drop3]; exact hf
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).mp h

end fubini

/-- Cauchy–Schwarz for two norms: `E √X√Y ≤ αβ` if `E X = α²`, `E Y = β²`. -/
theorem sqrt_pair_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hX0 : ∀ ω, 0 ≤ X ω) (hY0 : ∀ ω, 0 ≤ Y ω) (hXi : Integrable X μ) (hYi : Integrable Y μ)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hEX : ∫ ω, X ω ∂μ = α ^ 2) (hEY : ∫ ω, Y ω ∂μ = β ^ 2) :
    Integrable (fun ω => √(X ω) * √(Y ω)) μ ∧ ∫ ω, √(X ω) * √(Y ω) ∂μ ≤ α * β := by
  have hPm : Measurable (fun ω => √(X ω) * √(Y ω)) := hX.sqrt.mul hY.sqrt
  have hP0 : ∀ ω, 0 ≤ √(X ω) * √(Y ω) := fun ω =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hXY : Integrable (fun ω => (X ω + Y ω) / 2) μ := (hXi.add hYi).div_const 2
  have hPi : Integrable (fun ω => √(X ω) * √(Y ω)) μ := by
    refine Integrable.mono' hXY hPm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hP0 ω)]
    exact sqrt_mul_sqrt_le (hX0 ω) (hY0 ω)
  refine ⟨hPi, ?_⟩
  by_cases hdeg : α = 0 ∨ β = 0
  · have hP : (fun ω => √(X ω) * √(Y ω)) =ᵐ[μ] fun _ => (0 : ℝ) := by
      rcases hdeg with h | h
      · have h0 : ∫ ω, X ω ∂μ = 0 := by rw [hEX, h]; simp
        have := (integral_eq_zero_iff_of_nonneg hX0 hXi).mp h0
        filter_upwards [this] with ω hω
        have : X ω = 0 := hω
        simp [this]
      · have h0 : ∫ ω, Y ω ∂μ = 0 := by rw [hEY, h]; simp
        have := (integral_eq_zero_iff_of_nonneg hY0 hYi).mp h0
        filter_upwards [this] with ω hω
        have : Y ω = 0 := hω
        simp [this]
    rw [integral_congr_ae hP]
    simp only [integral_zero]
    exact mul_nonneg hα hβ
  · rw [not_or] at hdeg
    have hα' : 0 < α := lt_of_le_of_ne hα (Ne.symm hdeg.1)
    have hβ' : 0 < β := lt_of_le_of_ne hβ (Ne.symm hdeg.2)
    have hb : Integrable (fun ω => (β / α * X ω + α / β * Y ω) / 2) μ :=
      ((hXi.const_mul _).add (hYi.const_mul _)).div_const 2
    have hpt : ∀ ω, √(X ω) * √(Y ω) ≤ (β / α * X ω + α / β * Y ω) / 2 := by
      intro ω
      have h1 := Real.sq_sqrt (hX0 ω)
      have h2 := Real.sq_sqrt (hY0 ω)
      have h3 : β / α * X ω + α / β * Y ω - 2 * (√(X ω) * √(Y ω)) =
          (β * √(X ω) - α * √(Y ω)) ^ 2 / (α * β) := by
        field_simp
        nlinarith
      have h4 : 0 ≤ (β * √(X ω) - α * √(Y ω)) ^ 2 / (α * β) := by positivity
      linarith
    have h := integral_mono hPi hb hpt
    have a1 := integral_add (hXi.const_mul (β / α)) (hYi.const_mul (α / β))
    have a2 : ∫ ω, β / α * X ω ∂μ = β / α * ∫ ω, X ω ∂μ := integral_const_mul _ _
    have a3 : ∫ ω, α / β * Y ω ∂μ = α / β * ∫ ω, Y ω ∂μ := integral_const_mul _ _
    beta_reduce at a1
    rw [integral_div, a1, a2, a3, hEX, hEY] at h
    have e : (β / α * α ^ 2 + α / β * β ^ 2) / 2 = α * β := by field_simp; ring
    linarith

variable {k m₁ m₂ q : ℕ}

/-! ## The last hidden vector -/

lemma continuous_hid2_param (z : Fin k → ℝ) :
    Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      hid2 θ.1 θ.2 z) := by
  unfold hid2
  refine continuous_reluV.comp ?_
  refine Continuous.matrix_mulVec continuous_snd ?_
  refine continuous_reluV.comp ?_
  exact Continuous.matrix_mulVec continuous_fst continuous_const

/-- `E|h₂(z)|² = (m₂/2)v₂·(m₁/2)v₁·|z|²`. -/
theorem hid2_sq {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (z : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      normSq (hid2 θ.1 θ.2 z)) ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) ∧
    ∫ θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ, normSq (hid2 θ.1 θ.2 z)
      ∂((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) =
      (m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁) * normSq z := by
  have step := prod_step (μ := gaussMat m₁ k v₁) (ν := gaussMat m₂ m₁ v₂)
    (f := fun θ => normSq (hid2 θ.1 θ.2 z))
    (continuous_normSq.comp (continuous_hid2_param z)).measurable (fun p => normSq_nonneg _)
    (fun M₁ => (m₂ : ℝ) / 2 * (v₂ * normSq (reluV (M₁.mulVec z))))
    (fun M₁ => layer_relu_sq (m := m₂) h₂ (reluV (M₁.mulVec z)))
    (((layer_relu_sq (m := m₁) h₁ z).1.const_mul v₂).const_mul _)
  refine ⟨step.1, ?_⟩
  rw [step.2]
  have a1 : ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ, (m₂ : ℝ) / 2 * (v₂ * normSq (reluV (M₁.mulVec z)))
      ∂gaussMat m₁ k v₁ = (m₂ : ℝ) / 2 * ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      v₂ * normSq (reluV (M₁.mulVec z)) ∂gaussMat m₁ k v₁ := integral_const_mul _ _
  have a2 : ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ, v₂ * normSq (reluV (M₁.mulVec z))
      ∂gaussMat m₁ k v₁ = v₂ * ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      normSq (reluV (M₁.mulVec z)) ∂gaussMat m₁ k v₁ := integral_const_mul _ _
  rw [a1, a2, (layer_relu_sq h₁ z).2]
  ring

/-- `E|h₂(z)|⁴ = (m₂²/4 + 5m₂/4)v₂²·(m₁²/4 + 5m₁/4)v₁²·|z|⁴`. -/
theorem hid2_four {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (z : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      normSq (hid2 θ.1 θ.2 z) ^ 2) ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) ∧
    ∫ θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ, normSq (hid2 θ.1 θ.2 z) ^ 2
      ∂((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) =
      ((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2 * (((m₁ : ℝ) ^ 2 / 4 + 5 * m₁ / 4) * v₁ ^ 2) *
        normSq z ^ 2 := by
  have hgi : Integrable (fun M₁ : Matrix (Fin m₁) (Fin k) ℝ =>
      ((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * (v₂ * normSq (reluV (M₁.mulVec z))) ^ 2)
      (gaussMat m₁ k v₁) := by
    have e : (fun M₁ : Matrix (Fin m₁) (Fin k) ℝ =>
        ((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * (v₂ * normSq (reluV (M₁.mulVec z))) ^ 2) =
        fun M₁ => (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) *
          normSq (reluV (M₁.mulVec z)) ^ 2 := by
      funext M₁; ring
    rw [e]
    exact (layer_relu_four (m := m₁) h₁ z).1.const_mul _
  have step := prod_step (μ := gaussMat m₁ k v₁) (ν := gaussMat m₂ m₁ v₂)
    (f := fun θ => normSq (hid2 θ.1 θ.2 z) ^ 2)
    ((continuous_normSq.comp (continuous_hid2_param z)).pow 2).measurable (fun p => sq_nonneg _)
    (fun M₁ => ((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * (v₂ * normSq (reluV (M₁.mulVec z))) ^ 2)
    (fun M₁ => layer_relu_four (m := m₂) h₂ (reluV (M₁.mulVec z))) hgi
  refine ⟨step.1, ?_⟩
  rw [step.2]
  have e : (fun M₁ : Matrix (Fin m₁) (Fin k) ℝ =>
      ((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * (v₂ * normSq (reluV (M₁.mulVec z))) ^ 2) =
      fun M₁ => (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) *
        normSq (reluV (M₁.mulVec z)) ^ 2 := by
    funext M₁; ring
  have a1 : ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ, (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) *
      normSq (reluV (M₁.mulVec z)) ^ 2 ∂gaussMat m₁ k v₁ =
      (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) * ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      normSq (reluV (M₁.mulVec z)) ^ 2 ∂gaussMat m₁ k v₁ := integral_const_mul _ _
  rw [e, a1, (layer_relu_four h₁ z).2]
  ring

lemma hid2_dot_integrable {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (y y' : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y')) ((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) := by
  have hc : Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ =>
      dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y')) :=
    continuous_dotp.comp ((continuous_hid2_param y).prodMk (continuous_hid2_param y'))
  refine Integrable.mono' ((hid2_sq h₁ h₂ y).1.add (hid2_sq h₁ h₂ y').1)
    hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun θ => abs_dotp_le _ _)

/-- **The two hidden layers** (paper: "F_2 and F_3, then F_1"):
`E ⟨h₂(y), h₂(y′)⟩ ≥ (m₂/2)v₂·(m₁/2)v₁·[Ψ_{κ∘κ}(y, y′) − (10/m₁)·κ(0)·|y||y′|]`. -/
theorem hid2_dot_lower {v₁ v₂ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (hm₁ : 1 ≤ m₁)
    (y y' : Fin k → ℝ) :
    (m₂ : ℝ) / 2 * v₂ * ((m₁ : ℝ) / 2 * v₁ *
        (psi (kappa ∘ kappa) y y' - 10 / (m₁ : ℝ) * kappa 0 * (nrm y * nrm y'))) ≤
      ∫ θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ,
        dotp (hid2 θ.1 θ.2 y) (hid2 θ.1 θ.2 y') ∂((gaussMat m₁ k v₁).prod (gaussMat m₂ m₁ v₂)) := by
  obtain ⟨hi, hl⟩ := relu_layer_lower (m := m₁) kGood_kappa h₁ hm₁ y y'
  have key := integral_prod_ge (hid2_dot_integrable (m₂ := m₂) h₁ h₂ y y')
    (g := fun M₁ => (m₂ : ℝ) / 2 * v₂ * psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')))
    (hi.const_mul _) (fun M₁ => by
      have := (layer_dot_relu (m := m₂) h₂ (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))).2
      rw [kernelPhi_eq_psi] at this
      apply le_of_eq
      rw [← mul_assoc] at this
      exact this.symm)
  have a1 : ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ, (m₂ : ℝ) / 2 * v₂ *
      psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) ∂gaussMat m₁ k v₁ =
      (m₂ : ℝ) / 2 * v₂ * ∫ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      psi kappa (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y')) ∂gaussMat m₁ k v₁ :=
    integral_const_mul _ _
  rw [a1] at key
  refine le_trans (mul_le_mul_of_nonneg_left hl (by positivity)) key

/-! ## A whole network -/

/-- The last two matrices, for fixed first hidden vectors `g, g′`. -/
theorem tail_psi_lower {G : ℝ → ℝ} (hG : KGood G) {v₂ v₃ : ℝ} (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (hm₂ : 1 ≤ m₂) (hq : 1 ≤ q) (g g' : Fin m₁ → ℝ) :
    Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))))
      ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) ∧
    (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
        (psi (G ∘ kappa) g g' - (10 / (m₂ : ℝ) + 4 / (q : ℝ)) * G 0 * (nrm g * nrm g')) ≤
      ∫ θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ,
        psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g')))
        ∂((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) := by
  have hm' : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  -- integrability
  have hmeas : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g')))) := by
    have c : ∀ g : Fin m₁ → ℝ, Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => θ.2.mulVec (reluV (θ.1.mulVec g))) := fun g =>
      Continuous.matrix_mulVec continuous_snd
        (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const))
    exact Measurable.comp (g := fun p : (Fin q → ℝ) × (Fin q → ℝ) => psi G p.1 p.2)
      (f := fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (θ.2.mulVec (reluV (θ.1.mulVec g)), θ.2.mulVec (reluV (θ.1.mulVec g'))))
      (measurable_psi hG.cont) ((c g).prodMk (c g')).measurable
  have hsq : ∀ g : Fin m₁ → ℝ, Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ ×
      Matrix (Fin q) (Fin m₂) ℝ => normSq (θ.2.mulVec (reluV (θ.1.mulVec g))))
      ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) := by
    intro g
    have c : Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => θ.2.mulVec (reluV (θ.1.mulVec g))) :=
      Continuous.matrix_mulVec continuous_snd
        (continuous_reluV.comp (Continuous.matrix_mulVec continuous_fst continuous_const))
    exact (prod_step (μ := gaussMat m₂ m₁ v₂) (ν := gaussMat q m₂ v₃)
      (f := fun θ => normSq (θ.2.mulVec (reluV (θ.1.mulVec g))))
      (continuous_normSq.comp c).measurable (fun p => normSq_nonneg _)
      (fun M₂ => (q : ℝ) * (v₃ * normSq (reluV (M₂.mulVec g))))
      (fun M₂ => layer_lin_sq (m := q) h₃ (reluV (M₂.mulVec g)))
      (((layer_relu_sq (m := m₂) h₂ g).1.const_mul v₃).const_mul (q : ℝ))).1
  have hint : Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      psi G (θ.2.mulVec (reluV (θ.1.mulVec g))) (θ.2.mulVec (reluV (θ.1.mulVec g'))))
      ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) := by
    refine Integrable.mono' (((hsq g).add (hsq g')).div_const 2) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg hG _ _)]
    exact (psi_le_nrm hG _ _).trans (nrm_mul_le _ _)
  refine ⟨hint, ?_⟩
  obtain ⟨hRi, hRl⟩ := relu_layer_lower (m := m₂) hG h₂ hm₂ g g'
  obtain ⟨hPi, hPu, -, -, -⟩ := relu_layer_pair (m := m₂) h₂ hm₂ g g'
  have hgi : Integrable (fun M₂ : Matrix (Fin m₂) (Fin m₁) ℝ => (q : ℝ) * v₃ *
      (psi G (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')) - 4 / (q : ℝ) * G 0 *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g'))))) (gaussMat m₂ m₁ v₂) :=
    (hRi.sub (hPi.const_mul _)).const_mul _
  have key := integral_prod_ge hint hgi (fun M₂ =>
    (lin_layer_lower (m := q) hG h₃ hq (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g'))).2)
  have a1 : ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ, (q : ℝ) * v₃ *
      (psi G (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')) - 4 / (q : ℝ) * G 0 *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')))) ∂gaussMat m₂ m₁ v₂ =
      (q : ℝ) * v₃ * ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ,
      (psi G (reluV (M₂.mulVec g)) (reluV (M₂.mulVec g')) - 4 / (q : ℝ) * G 0 *
        (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')))) ∂gaussMat m₂ m₁ v₂ :=
    integral_const_mul _ _
  have a2 := integral_sub hRi (hPi.const_mul (4 / (q : ℝ) * G 0))
  have a3 : ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ, 4 / (q : ℝ) * G 0 *
      (nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g'))) ∂gaussMat m₂ m₁ v₂ =
      4 / (q : ℝ) * G 0 * ∫ M₂ : Matrix (Fin m₂) (Fin m₁) ℝ,
      nrm (reluV (M₂.mulVec g)) * nrm (reluV (M₂.mulVec g')) ∂gaussMat m₂ m₁ v₂ :=
    integral_const_mul _ _
  beta_reduce at a2
  rw [a1, a2, a3] at key
  refine le_trans ?_ key
  have hqv : 0 ≤ (q : ℝ) * v₃ := by positivity
  have hc : 0 ≤ 4 / (q : ℝ) * G 0 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hPu hc
  have h6 : (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
      (psi (G ∘ kappa) g g' - (10 / (m₂ : ℝ) + 4 / (q : ℝ)) * G 0 * (nrm g * nrm g')) =
      (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂ * (psi (G ∘ kappa) g g' - 10 / (m₂ : ℝ) * G 0 *
        (nrm g * nrm g')) - 4 / (q : ℝ) * G 0 * ((m₂ : ℝ) / 2 * v₂ * (nrm g * nrm g'))) := by
    ring
  rw [h6]
  exact mul_le_mul_of_nonneg_left (by linarith) hqv

lemma net_arith {s Ψ p0 I1 I2 d a b g0 : ℝ} (hRl : s * (Ψ - a * g0 * p0) ≤ I1)
    (h5 : d * I2 ≤ d * (s * p0)) (e3 : d * (s * p0) ≤ (a + b) * (s * p0))
    (e4 : a * g0 * (s * p0) ≤ a * (s * p0)) : s * (Ψ - (b + 2 * a) * p0) ≤ I1 - d * I2 := by
  nlinarith

lemma continuous_mlpEval_pair (z z' : Fin k → ℝ) {m : ℕ} :
    Continuous (fun θ : MlpParam k m q => (mlpEval θ z, mlpEval θ z')) :=
  (continuous_mlpEval_param z).prodMk (continuous_mlpEval_param z')

lemma measurable_psi_mlp {G : ℝ → ℝ} (hG : Continuous G) {m : ℕ} (z z' : Fin k → ℝ) :
    Measurable (fun θ : MlpParam k m q => psi G (mlpEval θ z) (mlpEval θ z')) :=
  Measurable.comp (g := fun p : (Fin q → ℝ) × (Fin q → ℝ) => psi G p.1 p.2)
    (f := fun θ : MlpParam k m q => (mlpEval θ z, mlpEval θ z'))
    (measurable_psi hG) (continuous_mlpEval_pair z z').measurable

/-- **A lower bound of the kernel through a whole random ReLU MLP** (two hidden layers of width
`m`, `q` outputs): `E Ψ_G(N(z), N(z′)) ≥ (2q/k)·[Ψ_{G∘κ∘κ}(z, z′) − ((4/q)·G(0) + 20/m)·|z||z′|]`.
-/
theorem mlp_psi_lower {G : ℝ → ℝ} (hG : KGood G) {m : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q)
    (z z' : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => psi G (mlpEval θ z) (mlpEval θ z')) (mlpGauss k m q) ∧
    2 * (q : ℝ) / k * (psi (G ∘ kappa ∘ kappa) z z' -
        (4 / (q : ℝ) * G 0 + 20 / (m : ℝ)) * (nrm z * nrm z')) ≤
      ∫ θ, psi G (mlpEval θ z) (mlpEval θ z') ∂mlpGauss k m q := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hG0 : 0 ≤ G 0 := hG.nonneg_on KGood.zero_mem
  have hG1 : G 0 ≤ 1 := hG.le_one KGood.zero_mem
  have hGk := hG.comp_kappa
  have hGk0 : 0 ≤ (G ∘ kappa) 0 := hGk.nonneg_on KGood.zero_mem
  have hGk1 : (G ∘ kappa) 0 ≤ 1 := hGk.le_one KGood.zero_mem
  have hint : Integrable (fun θ : MlpParam k m q => psi G (mlpEval θ z) (mlpEval θ z'))
      (mlpGauss k m q) := by
    refine Integrable.mono' (((mlp_normSq_integrable z).add (mlp_normSq_integrable z')).div_const 2)
      (measurable_psi_mlp hG.cont z z').aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (psi_nonneg hG _ _)]
    exact (psi_le_nrm hG _ _).trans (nrm_mul_le _ _)
  refine ⟨hint, ?_⟩
  have h1 : (0 : ℝ) ≤ 2 / (k : ℝ) := two_div_nonneg k
  have h2 : (0 : ℝ) ≤ 2 / (m : ℝ) := two_div_nonneg m
  obtain ⟨hRi, hRl⟩ := relu_layer_lower (m := m) hGk h1 hm z z'
  obtain ⟨hPi, hPu, -, -, -⟩ := relu_layer_pair (m := m) h1 hm z z'
  set c : ℝ := (q : ℝ) * (2 / (m : ℝ)) * ((m : ℝ) / 2 * (2 / (m : ℝ))) with hc
  have hc0 : 0 ≤ c := by positivity
  have hgi : Integrable (fun M₁ : Matrix (Fin m) (Fin k) ℝ => c *
      (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) -
        (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 *
          (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))))) (gaussMat m k (2 / (k : ℝ))) :=
    (hRi.sub (hPi.const_mul _)).const_mul _
  unfold mlpGauss at hint ⊢
  have key := integral_prod_ge hint hgi (fun M₁ =>
    (tail_psi_lower (m₂ := m) (q := q) hG h2 h2 hm hq (reluV (M₁.mulVec z))
      (reluV (M₁.mulVec z'))).2)
  have a1 : ∫ M₁ : Matrix (Fin m) (Fin k) ℝ, c *
      (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) -
        (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 *
          (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z')))) ∂gaussMat m k (2 / (k : ℝ)) =
      c * ∫ M₁ : Matrix (Fin m) (Fin k) ℝ,
      (psi (G ∘ kappa) (reluV (M₁.mulVec z)) (reluV (M₁.mulVec z')) -
        (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 *
          (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z')))) ∂gaussMat m k (2 / (k : ℝ)) :=
    integral_const_mul _ _
  have a2 := integral_sub hRi (hPi.const_mul ((10 / (m : ℝ) + 4 / (q : ℝ)) * G 0))
  have a3 : ∫ M₁ : Matrix (Fin m) (Fin k) ℝ, (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 *
      (nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z'))) ∂gaussMat m k (2 / (k : ℝ)) =
      (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 * ∫ M₁ : Matrix (Fin m) (Fin k) ℝ,
      nrm (reluV (M₁.mulVec z)) * nrm (reluV (M₁.mulVec z')) ∂gaussMat m k (2 / (k : ℝ)) :=
    integral_const_mul _ _
  beta_reduce at a2
  rw [a1, a2, a3] at key
  refine le_trans ?_ key
  have hd : 0 ≤ (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 := by positivity
  have h5 := mul_le_mul_of_nonneg_left hPu hd
  have hp0 := nrm_mul_nonneg z z'
  have hs : 0 ≤ (m : ℝ) / 2 * (2 / (k : ℝ)) := by positivity
  have hce : c * ((m : ℝ) / 2 * (2 / (k : ℝ))) = 2 * (q : ℝ) / k := by
    rw [hc]; field_simp
  have hcomp : psi (G ∘ kappa ∘ kappa) z z' = psi ((G ∘ kappa) ∘ kappa) z z' := rfl
  rw [← hce, hcomp, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc0
  -- compare the two error terms
  have e1 : (10 / (m : ℝ) + 4 / (q : ℝ)) * G 0 ≤ 10 / (m : ℝ) + 4 / (q : ℝ) * G 0 := by
    have : 10 / (m : ℝ) * G 0 ≤ 10 / (m : ℝ) := by
      have h10 : (0 : ℝ) ≤ 10 / (m : ℝ) := by positivity
      nlinarith
    linarith
  have e2 : 10 / (m : ℝ) * (G ∘ kappa) 0 ≤ 10 / (m : ℝ) := by
    have h10 : (0 : ℝ) ≤ 10 / (m : ℝ) := by positivity
    nlinarith
  have hsp : 0 ≤ (m : ℝ) / 2 * (2 / (k : ℝ)) * (nrm z * nrm z') := mul_nonneg hs hp0
  have e3 := mul_le_mul_of_nonneg_right e1 hsp
  have e4 := mul_le_mul_of_nonneg_right e2 hsp
  have h20 : (4 / (q : ℝ) * G 0 + 20 / (m : ℝ)) = (4 / (q : ℝ) * G 0 + 2 * (10 / (m : ℝ))) := by
    ring
  rw [h20]
  exact net_arith hRl h5 e3 e4

/-- `E |N(z)||N(z′)| ≤ (2q/k)·|z||z′|` (Cauchy–Schwarz and the exact second moment). -/
theorem mlp_nrm_upper {m : ℕ} (hm : 1 ≤ m) (z z' : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => nrm (mlpEval θ z) * nrm (mlpEval θ z'))
      (mlpGauss k m q) ∧
    ∫ θ : MlpParam k m q, nrm (mlpEval θ z) * nrm (mlpEval θ z') ∂mlpGauss k m q ≤
      2 * (q : ℝ) / k * (nrm z * nrm z') := by
  have hs : (0 : ℝ) ≤ 2 * (q : ℝ) / k := by positivity
  have hmeas : ∀ z : Fin k → ℝ, Measurable (fun θ : MlpParam k m q => normSq (mlpEval θ z)) :=
    fun z => (continuous_normSq.comp (continuous_mlpEval_param z)).measurable
  have hsq : ∀ z : Fin k → ℝ, ∫ θ : MlpParam k m q, normSq (mlpEval θ z) ∂mlpGauss k m q =
      (√(2 * (q : ℝ) / k) * nrm z) ^ 2 := by
    intro z
    rw [mlp_second_moment hm, mul_pow, Real.sq_sqrt hs, nrm_sq]
  have key := sqrt_pair_le (μ := mlpGauss k m q) (hmeas z) (hmeas z')
    (fun θ => normSq_nonneg _) (fun θ => normSq_nonneg _) (mlp_normSq_integrable z)
    (mlp_normSq_integrable z') (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg z))
    (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg z')) (hsq z) (hsq z')
  refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
  have := Real.mul_self_sqrt hs
  calc _ = (√(2 * (q : ℝ) / k) * √(2 * (q : ℝ) / k)) * (nrm z * nrm z') := by ring
    _ = _ := by rw [this]

end BstLean.Part132

open BstLean.Part132 in
#print axioms hid2_dot_lower
open BstLean.Part132 in
#print axioms mlp_psi_lower
open BstLean.Part132 in
#print axioms mlp_nrm_upper
