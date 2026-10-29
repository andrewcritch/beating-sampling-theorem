import BstLean.Part130Moments

/-!
# Part 130, item 2: the exact second and fourth moments of a random ReLU MLP

Paper source: `delegations/answers/onW2c-cx.md` §1.
For every input `z`, hidden width `m ≥ 1`:
* `mlp_second_moment`: `E|N(z)|² = (2q/k)·|z|²`;
* `mlp_fourth_moment`: `E|N(z)|⁴ = ((2q/k)|z|²)²·(1 + 5/m)·(1 + 5/m)·(1 + 2/q)`.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)

/-- Fubini for a nonnegative function whose inner integral is known. -/
lemma prod_step {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {f : α × β → ℝ} (hf : Measurable f)
    (h0 : ∀ p, 0 ≤ f p) (g : α → ℝ)
    (h1 : ∀ x, Integrable (fun y => f (x, y)) ν ∧ ∫ y, f (x, y) ∂ν = g x)
    (hg : Integrable g μ) :
    Integrable f (μ.prod ν) ∧ ∫ p, f p ∂(μ.prod ν) = ∫ x, g x ∂μ := by
  have hi : Integrable f (μ.prod ν) := by
    rw [integrable_prod_iff hf.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => (h1 x).1, ?_⟩
    have : (fun x => ∫ y, ‖f (x, y)‖ ∂ν) = g := by
      funext x
      rw [← (h1 x).2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp [abs_of_nonneg (h0 (x, y))])
    rw [this]
    exact hg
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (h1 x).2)

variable {k m₁ m₂ q : ℕ}

instance instSecondCountableMatrix (a b : ℕ) : SecondCountableTopology (Matrix (Fin a) (Fin b) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → ℝ))

lemma continuous_mlp2 (z : Fin k → ℝ) :
    Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
      Matrix (Fin q) (Fin m₂) ℝ => mlp2 θ.1 θ.2.1 θ.2.2 z) := by
  unfold mlp2
  refine Continuous.matrix_mulVec (by fun_prop) ?_
  refine continuous_reluV.comp ?_
  refine Continuous.matrix_mulVec (by fun_prop) ?_
  refine continuous_reluV.comp ?_
  exact Continuous.matrix_mulVec (by fun_prop) continuous_const

lemma continuous_normSq_mlp2_inner (z : Fin k → ℝ) (M₁ : Matrix (Fin m₁) (Fin k) ℝ) :
    Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      normSq (mlp2 M₁ θ.1 θ.2 z)) := by
  have hcont := continuous_mlp2 (m₁ := m₁) (m₂ := m₂) (q := q) z
  have h2 : Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
      (M₁, θ)) := by fun_prop
  exact continuous_normSq.comp (hcont.comp h2)

/-- The general form, with three variances and two hidden widths: second moment. -/
theorem mlp2_second_moment_gen {v₁ v₂ v₃ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (z : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 θ.1 θ.2.1 θ.2.2 z))
      ((gaussMat m₁ k v₁).prod ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))) ∧
    ∫ θ, normSq (mlp2 θ.1 θ.2.1 θ.2.2 z)
      ∂((gaussMat m₁ k v₁).prod ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))) =
      (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) * ((m₁ : ℝ) / 2 * v₁) * normSq z := by
  have hcont := continuous_mlp2 (m₁ := m₁) (m₂ := m₂) (q := q) z
  have hmeas : Measurable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
      Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 θ.1 θ.2.1 θ.2.2 z)) :=
    (continuous_normSq.comp hcont).measurable
  -- inner step, `M₁` fixed
  have inner : ∀ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        normSq (mlp2 M₁ θ.1 θ.2 z)) ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) ∧
      ∫ θ, normSq (mlp2 M₁ θ.1 θ.2 z) ∂((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) =
        (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) * normSq (reluV (M₁.mulVec z)) := by
    intro M₁
    have hm : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        normSq (mlp2 M₁ θ.1 θ.2 z)) := (continuous_normSq_mlp2_inner z M₁).measurable
    have step := prod_step (μ := gaussMat m₂ m₁ v₂) (ν := gaussMat q m₂ v₃) hm
      (fun p => normSq_nonneg _)
      (fun M₂ => (q : ℝ) * (v₃ * normSq (reluV (M₂.mulVec (reluV (M₁.mulVec z))))))
      (fun M₂ => layer_lin_sq (m := q) h₃ (reluV (M₂.mulVec (reluV (M₁.mulVec z)))))
      (((layer_relu_sq (m := m₂) h₂ (reluV (M₁.mulVec z))).1.const_mul v₃).const_mul (q : ℝ))
    refine ⟨step.1, ?_⟩
    rw [step.2]
    simp_rw [← mul_assoc]
    rw [integral_const_mul, (layer_relu_sq (m := m₂) h₂ (reluV (M₁.mulVec z))).2]
    ring
  have step := prod_step (μ := gaussMat m₁ k v₁)
    (ν := (gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) hmeas (fun p => normSq_nonneg _)
    (fun M₁ => (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) * normSq (reluV (M₁.mulVec z)))
    inner ((layer_relu_sq h₁ z).1.const_mul _)
  refine ⟨step.1, ?_⟩
  rw [step.2, integral_const_mul, (layer_relu_sq h₁ z).2]
  ring

/-- The general form: fourth moment. -/
theorem mlp2_fourth_moment_gen {v₁ v₂ v₃ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (z : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 θ.1 θ.2.1 θ.2.2 z) ^ 2)
      ((gaussMat m₁ k v₁).prod ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))) ∧
    ∫ θ, normSq (mlp2 θ.1 θ.2.1 θ.2.2 z) ^ 2
      ∂((gaussMat m₁ k v₁).prod ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))) =
      (((q : ℝ) ^ 2 + 2 * q) * v₃ ^ 2) * (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) *
        (((m₁ : ℝ) ^ 2 / 4 + 5 * m₁ / 4) * v₁ ^ 2) * normSq z ^ 2 := by
  have hcont := continuous_mlp2 (m₁ := m₁) (m₂ := m₂) (q := q) z
  have hmeas : Measurable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
      Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 θ.1 θ.2.1 θ.2.2 z) ^ 2) :=
    ((continuous_normSq.comp hcont).pow 2).measurable
  have inner : ∀ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        normSq (mlp2 M₁ θ.1 θ.2 z) ^ 2) ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) ∧
      ∫ θ, normSq (mlp2 M₁ θ.1 θ.2 z) ^ 2 ∂((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) =
        (((q : ℝ) ^ 2 + 2 * q) * v₃ ^ 2) * (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) *
          normSq (reluV (M₁.mulVec z)) ^ 2 := by
    intro M₁
    have hm : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        normSq (mlp2 M₁ θ.1 θ.2 z) ^ 2) := ((continuous_normSq_mlp2_inner z M₁).pow 2).measurable
    have step := prod_step (μ := gaussMat m₂ m₁ v₂) (ν := gaussMat q m₂ v₃) hm
      (fun p => sq_nonneg _)
      (fun M₂ => (((q : ℝ) ^ 2 + 2 * q) * v₃ ^ 2) *
        normSq (reluV (M₂.mulVec (reluV (M₁.mulVec z)))) ^ 2)
      (fun M₂ => ⟨(layer_lin_four (m := q) h₃ (reluV (M₂.mulVec (reluV (M₁.mulVec z))))).1, by
        rw [show (fun y : Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 M₁ M₂ y z) ^ 2) =
          fun y => normSq (y.mulVec (reluV (M₂.mulVec (reluV (M₁.mulVec z))))) ^ 2 from rfl,
          (layer_lin_four (m := q) h₃ (reluV (M₂.mulVec (reluV (M₁.mulVec z))))).2]; ring⟩)
      ((layer_relu_four (m := m₂) h₂ (reluV (M₁.mulVec z))).1.const_mul _)
    refine ⟨step.1, ?_⟩
    rw [step.2, integral_const_mul, (layer_relu_four (m := m₂) h₂ (reluV (M₁.mulVec z))).2]
    ring
  have step := prod_step (μ := gaussMat m₁ k v₁)
    (ν := (gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) hmeas (fun p => sq_nonneg _)
    (fun M₁ => (((q : ℝ) ^ 2 + 2 * q) * v₃ ^ 2) * (((m₂ : ℝ) ^ 2 / 4 + 5 * m₂ / 4) * v₂ ^ 2) *
          normSq (reluV (M₁.mulVec z)) ^ 2)
    inner ((layer_relu_four h₁ z).1.const_mul _)
  refine ⟨step.1, ?_⟩
  rw [step.2, integral_const_mul, (layer_relu_four h₁ z).2]
  ring

variable {m : ℕ}

lemma two_div_nonneg (k : ℕ) : (0 : ℝ) ≤ 2 / (k : ℝ) := by positivity

/-- `|N(z)|²` is integrable under the random MLP distribution. -/
theorem mlp_normSq_integrable (z : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => normSq (mlpEval θ z)) (mlpGauss k m q) :=
  (mlp2_second_moment_gen (m₁ := m) (m₂ := m) (two_div_nonneg k) (two_div_nonneg m) (two_div_nonneg m) z).1

/-- **The exact second moment**: `E|N(z)|² = (2q/k)·|z|²`, for every `z` and every hidden width
`m ≥ 1`. -/
theorem mlp_second_moment (hm : 1 ≤ m) (z : Fin k → ℝ) :
    ∫ θ, normSq (mlpEval θ z) ∂mlpGauss k m q = 2 * (q : ℝ) / k * normSq z := by
  have h := (mlp2_second_moment_gen (m₁ := m) (m₂ := m) (q := q) (two_div_nonneg k) (two_div_nonneg m)
    (two_div_nonneg m) z).2
  unfold mlpGauss mlpEval
  rw [h]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- `|N(z)|⁴` is integrable under the random MLP distribution. -/
theorem mlp_normSq_sq_integrable (z : Fin k → ℝ) :
    Integrable (fun θ : MlpParam k m q => normSq (mlpEval θ z) ^ 2) (mlpGauss k m q) :=
  (mlp2_fourth_moment_gen (m₁ := m) (m₂ := m) (two_div_nonneg k) (two_div_nonneg m) (two_div_nonneg m) z).1

/-- **The exact fourth moment**:
`E|N(z)|⁴ = ((2q/k)|z|²)²·(1 + 5/m)·(1 + 5/m)·(1 + 2/q)`, for every `z` and `m ≥ 1`. -/
theorem mlp_fourth_moment (hm : 1 ≤ m) (z : Fin k → ℝ) :
    ∫ θ, normSq (mlpEval θ z) ^ 2 ∂mlpGauss k m q =
      (2 * (q : ℝ) / k * normSq z) ^ 2 * (1 + 5 / (m : ℝ)) * (1 + 5 / (m : ℝ)) *
        (1 + 2 / (q : ℝ)) := by
  have h := (mlp2_fourth_moment_gen (m₁ := m) (m₂ := m) (q := q) (two_div_nonneg k) (two_div_nonneg m)
    (two_div_nonneg m) z).2
  unfold mlpGauss mlpEval
  rw [h]
  have hm' : (m : ℝ) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hk' : (k : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `E|A(z)|² = 2|z|²` for the Agent network (`k = q = n`, `n ≥ 1`). -/
theorem agent_second_moment {n : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (z : Fin n → ℝ) :
    ∫ A, normSq (mlpEval A z) ∂mlpGauss n m n = 2 * normSq z := by
  rw [mlp_second_moment hm]
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- `E F(y)² = 2|y|²/n` for the network `F` (`q = 1`). -/
theorem F_second_moment {n : ℕ} (hm : 1 ≤ m) (y : Fin n → ℝ) :
    ∫ F, (mlpEval F y 0) ^ 2 ∂mlpGauss n m 1 = 2 * normSq y / n := by
  have h := mlp_second_moment (q := 1) hm y
  simp only [normSq, Fin.sum_univ_one, Nat.cast_one, mul_one] at h
  rw [h]
  simp only [normSq]
  ring

end BstLean.Part130

open BstLean.Part130 in
#print axioms mlp_second_moment
open BstLean.Part130 in
#print axioms mlp_fourth_moment
open BstLean.Part130 in
#print axioms agent_second_moment
open BstLean.Part130 in
#print axioms F_second_moment
