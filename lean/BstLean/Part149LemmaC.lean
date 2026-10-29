import BstLean.Part130All
import BstLean.Part133L2

/-!
# Part 149, Lemma C: a random ReLU MLP is Lipschitz in mean square

Do not use `sorry`, `native_decide` or `axiom`.

* `relu_lip_sq` (Lemma R): `(relu g − relu g')² + (relu (−g) − relu (−g'))² ≤ (g − g')²`.
* `layer_lip`: `E|ReLU(M h) − ReLU(M h')|² ≤ (m/2)·v·|h − h'|²` for a Gaussian matrix `M`
  (`m` rows, entry variance `v`).
* `prod_step_le`: Fubini for a nonnegative function whose inner integral has a known upper bound.
* `mlp2_lip_gen`: the general form with three variances and two hidden widths.
* `lemmaC_pt`: `E_F (F(y) − F(y'))² ≤ (2/n)·|y − y'|²`.
* `lemmaC_prod`: `E_{F, ω} (F(X) − F(Y))² ≤ (2/n)·E|X − Y|²`.
* `lemmaC149`: `E_F (E_ω (F(X) − F(Y)))² ≤ (2/n)·E|X − Y|²` (the coupling form).
* `lemmaC_gauss`: `E_{F, ξ} (F(a + sξ) − F(a))² ≤ 2s²`, `ξ` standard Gaussian in `ℝⁿ`.
-/

namespace BstLean.Part149

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss gaussMom gaussMom_eq)
open BstLean.Part130 BstLean.Part133

/-! ## Lemma R -/

/-- **Lemma R**: `(relu g − relu g')² + (relu (−g) − relu (−g'))² ≤ (g − g')²`. -/
lemma relu_lip_sq (g g' : ℝ) :
    (relu g - relu g') ^ 2 + (relu (-g) - relu (-g')) ^ 2 ≤ (g - g') ^ 2 := by
  rcases le_total 0 g with hg | hg <;> rcases le_total 0 g' with hg' | hg'
  · rw [relu_of_nonneg hg, relu_of_nonneg hg', relu_of_nonpos (neg_nonpos.2 hg),
      relu_of_nonpos (neg_nonpos.2 hg')]
    nlinarith
  · rw [relu_of_nonneg hg, relu_of_nonpos hg', relu_of_nonpos (neg_nonpos.2 hg),
      relu_of_nonneg (neg_nonneg.2 hg')]
    nlinarith [mul_nonneg hg (neg_nonneg.2 hg')]
  · rw [relu_of_nonpos hg, relu_of_nonneg hg', relu_of_nonneg (neg_nonneg.2 hg),
      relu_of_nonpos (neg_nonpos.2 hg')]
    nlinarith [mul_nonneg hg' (neg_nonneg.2 hg)]
  · rw [relu_of_nonpos hg, relu_of_nonpos hg', relu_of_nonneg (neg_nonneg.2 hg),
      relu_of_nonneg (neg_nonneg.2 hg')]
    nlinarith

/-- Lemma R for vectors. -/
lemma reluV_lip_sq {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    normSq (reluV a - reluV b) + normSq (reluV (-a) - reluV (-b)) ≤ normSq (a - b) := by
  unfold normSq
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => relu_lip_sq (a i) (b i)

/-! ## One layer -/

/-- **One layer is Lipschitz in mean square**:
`E|ReLU(M h) − ReLU(M h')|² ≤ (m/2)·v·|h − h'|²`. -/
theorem layer_lip {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
        normSq (reluV (M.mulVec h) - reluV (M.mulVec h'))) (gaussMat m k v) ∧
    ∫ M, normSq (reluV (M.mulVec h) - reluV (M.mulVec h')) ∂gaussMat m k v ≤
      (m : ℝ) / 2 * (v * normSq (h - h')) := by
  set f : Matrix (Fin m) (Fin k) ℝ → ℝ :=
    fun M => normSq (reluV (M.mulVec h) - reluV (M.mulVec h')) with hf
  have hfm : Measurable f :=
    measurable_normSq.comp ((measurable_reluV.comp (measurable_mulVec_right h)).sub
      (measurable_reluV.comp (measurable_mulVec_right h')))
  have hlin := layer_lin_sq (m := m) hv (h - h')
  have hpt : ∀ M : Matrix (Fin m) (Fin k) ℝ, f M + f (-M) ≤ normSq (M.mulVec (h - h')) := by
    intro M
    have := reluV_lip_sq (M.mulVec h) (M.mulVec h')
    simp only [hf, Matrix.neg_mulVec, Matrix.mulVec_sub]
    exact this
  have hf0 : ∀ M, 0 ≤ f M := fun M => normSq_nonneg _
  have hfi : Integrable f (gaussMat m k v) := by
    refine hlin.1.mono' hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 M)]
    linarith [hpt M, hf0 (-M)]
  refine ⟨hfi, ?_⟩
  have hneg : ∫ M, f (-M) ∂gaussMat m k v = ∫ M, f M ∂gaussMat m k v := by
    have h1 := integral_map (μ := gaussMat m k v)
      (φ := fun M : Matrix (Fin m) (Fin k) ℝ => -M) measurable_neg.aemeasurable
      (f := f) hfm.aestronglyMeasurable
    rw [gaussMat_neg] at h1
    exact h1.symm
  have hfi' : Integrable (fun M => f (-M)) (gaussMat m k v) := by
    refine hlin.1.mono' (hfm.comp measurable_neg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun M => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 (-M))]
    linarith [hpt M, hf0 M]
  have hsum : ∫ M, (f M + f (-M)) ∂gaussMat m k v ≤ (m : ℝ) * (v * normSq (h - h')) := by
    rw [← hlin.2]
    exact integral_mono (hfi.add hfi') hlin.1 hpt
  rw [integral_add hfi hfi', hneg] at hsum
  linarith

/-! ## Fubini with an upper bound -/

/-- Fubini for a nonnegative function whose inner integral has a known upper bound. -/
lemma prod_step_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {f : α × β → ℝ} (hf : Measurable f)
    (h0 : ∀ p, 0 ≤ f p) (g : α → ℝ)
    (h1 : ∀ x, Integrable (fun y => f (x, y)) ν ∧ ∫ y, f (x, y) ∂ν ≤ g x)
    (hg : Integrable g μ) :
    Integrable f (μ.prod ν) ∧ ∫ p, f p ∂(μ.prod ν) ≤ ∫ x, g x ∂μ := by
  have hi : Integrable f (μ.prod ν) := by
    rw [integrable_prod_iff hf.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => (h1 x).1, ?_⟩
    have hsm : StronglyMeasurable (fun x => ∫ y, ‖f (x, y)‖ ∂ν) :=
      (hf.norm.stronglyMeasurable).integral_prod_right'
    refine hg.mono' hsm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have e : ∫ y, ‖f (x, y)‖ ∂ν = ∫ y, f (x, y) ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp [abs_of_nonneg (h0 (x, y))])
    rw [e, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => h0 (x, y))]
    exact (h1 x).2
  refine ⟨hi, ?_⟩
  rw [integral_prod _ hi]
  exact integral_mono hi.integral_prod_left hg fun x => (h1 x).2

/-! ## The network -/

lemma mlp2_sub {k m₁ m₂ q : ℕ} (M₁ : Matrix (Fin m₁) (Fin k) ℝ)
    (M₂ : Matrix (Fin m₂) (Fin m₁) ℝ) (M₃ : Matrix (Fin q) (Fin m₂) ℝ) (y y' : Fin k → ℝ) :
    mlp2 M₁ M₂ M₃ y - mlp2 M₁ M₂ M₃ y' =
      M₃.mulVec (reluV (M₂.mulVec (reluV (M₁.mulVec y))) -
        reluV (M₂.mulVec (reluV (M₁.mulVec y')))) := by
  unfold mlp2
  rw [Matrix.mulVec_sub]

/-- The general form, with three variances and two hidden widths. -/
theorem mlp2_lip_gen {k m₁ m₂ q : ℕ} {v₁ v₂ v₃ : ℝ} (h₁ : 0 ≤ v₁) (h₂ : 0 ≤ v₂) (h₃ : 0 ≤ v₃)
    (y y' : Fin k → ℝ) :
    Integrable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
        Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 θ.1 θ.2.1 θ.2.2 y - mlp2 θ.1 θ.2.1 θ.2.2 y'))
      ((gaussMat m₁ k v₁).prod ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))) ∧
    ∫ θ, normSq (mlp2 θ.1 θ.2.1 θ.2.2 y - mlp2 θ.1 θ.2.1 θ.2.2 y')
      ∂((gaussMat m₁ k v₁).prod ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃))) ≤
      (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) * ((m₁ : ℝ) / 2 * v₁) * normSq (y - y') := by
  have hc : ∀ z : Fin k → ℝ, Continuous (fun θ : Matrix (Fin m₁) (Fin k) ℝ ×
      Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ => mlp2 θ.1 θ.2.1 θ.2.2 z) :=
    fun z => continuous_mlp2 z
  have hmeas : Measurable (fun θ : Matrix (Fin m₁) (Fin k) ℝ × Matrix (Fin m₂) (Fin m₁) ℝ ×
      Matrix (Fin q) (Fin m₂) ℝ => normSq (mlp2 θ.1 θ.2.1 θ.2.2 y - mlp2 θ.1 θ.2.1 θ.2.2 y')) :=
    (continuous_normSq.comp ((hc y).sub (hc y'))).measurable
  have hC : (0 : ℝ) ≤ (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) := by positivity
  have inner : ∀ M₁ : Matrix (Fin m₁) (Fin k) ℝ,
      Integrable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        normSq (mlp2 M₁ θ.1 θ.2 y - mlp2 M₁ θ.1 θ.2 y'))
        ((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) ∧
      ∫ θ, normSq (mlp2 M₁ θ.1 θ.2 y - mlp2 M₁ θ.1 θ.2 y')
        ∂((gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) ≤
        (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
          normSq (reluV (M₁.mulVec y) - reluV (M₁.mulVec y')) := by
    intro M₁
    have h2 : Continuous (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        (M₁, θ)) := by fun_prop
    have hm : Measurable (fun θ : Matrix (Fin m₂) (Fin m₁) ℝ × Matrix (Fin q) (Fin m₂) ℝ =>
        normSq (mlp2 M₁ θ.1 θ.2 y - mlp2 M₁ θ.1 θ.2 y')) :=
      (continuous_normSq.comp (((hc y).comp h2).sub ((hc y').comp h2))).measurable
    have hl := layer_lip (m := m₂) h₂ (reluV (M₁.mulVec y)) (reluV (M₁.mulVec y'))
    have step := prod_step_le (μ := gaussMat m₂ m₁ v₂) (ν := gaussMat q m₂ v₃) hm
      (fun p => normSq_nonneg _)
      (fun M₂ => (q : ℝ) * (v₃ * normSq (reluV (M₂.mulVec (reluV (M₁.mulVec y))) -
        reluV (M₂.mulVec (reluV (M₁.mulVec y'))))))
      (fun M₂ => by
        have hl3 := layer_lin_sq (m := q) h₃ (reluV (M₂.mulVec (reluV (M₁.mulVec y))) -
          reluV (M₂.mulVec (reluV (M₁.mulVec y'))))
        simp only [mlp2_sub]
        exact ⟨hl3.1, hl3.2.le⟩)
      ((hl.1.const_mul v₃).const_mul (q : ℝ))
    refine ⟨step.1, step.2.trans ?_⟩
    simp_rw [← mul_assoc]
    rw [integral_const_mul]
    have hqv : (0 : ℝ) ≤ (q : ℝ) * v₃ := by positivity
    calc (q : ℝ) * v₃ * ∫ M₂, normSq (reluV (M₂.mulVec (reluV (M₁.mulVec y))) -
            reluV (M₂.mulVec (reluV (M₁.mulVec y')))) ∂gaussMat m₂ m₁ v₂
        ≤ (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 *
            (v₂ * normSq (reluV (M₁.mulVec y) - reluV (M₁.mulVec y')))) :=
          mul_le_mul_of_nonneg_left hl.2 hqv
      _ = _ := by ring
  have hl1 := layer_lip (m := m₁) h₁ y y'
  have step := prod_step_le (μ := gaussMat m₁ k v₁)
    (ν := (gaussMat m₂ m₁ v₂).prod (gaussMat q m₂ v₃)) hmeas (fun p => normSq_nonneg _)
    (fun M₁ => (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
      normSq (reluV (M₁.mulVec y) - reluV (M₁.mulVec y')))
    inner (hl1.1.const_mul _)
  refine ⟨step.1, step.2.trans ?_⟩
  rw [integral_const_mul]
  calc (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) *
        ∫ M₁, normSq (reluV (M₁.mulVec y) - reluV (M₁.mulVec y')) ∂gaussMat m₁ k v₁
      ≤ (q : ℝ) * v₃ * ((m₂ : ℝ) / 2 * v₂) * ((m₁ : ℝ) / 2 * (v₁ * normSq (y - y'))) :=
        mul_le_mul_of_nonneg_left hl1.2 hC
    _ = _ := by ring

lemma sq_sub_eq_normSq {n m : ℕ} (F : MlpParam n m 1) (y y' : Fin n → ℝ) :
    (mlpEval F y 0 - mlpEval F y' 0) ^ 2 = normSq (mlpEval F y - mlpEval F y') := by
  simp [normSq]

/-- **Lemma C, pointwise**: `E_F (F(y) − F(y'))² ≤ (2/n)·|y − y'|²`. -/
theorem lemmaC_pt {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (y y' : Fin n → ℝ) :
    Integrable (fun F : MlpParam n m 1 => (mlpEval F y 0 - mlpEval F y' 0) ^ 2) (mlpGauss n m 1) ∧
    ∫ F, (mlpEval F y 0 - mlpEval F y' 0) ^ 2 ∂mlpGauss n m 1 ≤ 2 / (n : ℝ) * normSq (y - y') := by
  have h := mlp2_lip_gen (m₁ := m) (m₂ := m) (q := 1) (two_div_nonneg n) (two_div_nonneg m)
    (two_div_nonneg m) y y'
  simp_rw [sq_sub_eq_normSq]
  unfold mlpGauss mlpEval
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

/-! ## The coupling form -/

lemma measurable_evalDiff {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} {X Y : Ω → Fin n → ℝ}
    (hX : Measurable X) (hY : Measurable Y) :
    Measurable (fun p : MlpParam n m 1 × Ω => mlpEval p.1 (X p.2) 0 - mlpEval p.1 (Y p.2) 0) := by
  have hj : Measurable (fun p : MlpParam n m 1 × (Fin n → ℝ) => mlpEval p.1 p.2 0) :=
    ((continuous_apply 0).comp continuous_mlpEval_joint).measurable
  exact (hj.comp (measurable_fst.prodMk (hX.comp measurable_snd))).sub
    (hj.comp (measurable_fst.prodMk (hY.comp measurable_snd)))

/-- **Lemma C on the product space**: `E_{F, ω} (F(X) − F(Y))² ≤ (2/n)·E|X − Y|²`. -/
theorem lemmaC_prod {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {X Y : Ω → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) :
    Integrable (fun p : MlpParam n m 1 × Ω => (mlpEval p.1 (X p.2) 0 - mlpEval p.1 (Y p.2) 0) ^ 2)
        ((mlpGauss n m 1).prod P) ∧
    ∫ p, (mlpEval p.1 (X p.2) 0 - mlpEval p.1 (Y p.2) 0) ^ 2 ∂((mlpGauss n m 1).prod P) ≤
      2 / (n : ℝ) * ∫ ω, normSq (X ω - Y ω) ∂P := by
  set f : MlpParam n m 1 × Ω → ℝ :=
    fun p => (mlpEval p.1 (X p.2) 0 - mlpEval p.1 (Y p.2) 0) ^ 2 with hf
  have hfm : Measurable f := (measurable_evalDiff hX hY).pow_const 2
  have step := prod_step_le (μ := P) (ν := mlpGauss n m 1) (f := fun p => f p.swap)
    (hfm.comp measurable_swap) (fun p => sq_nonneg _)
    (fun ω => 2 / (n : ℝ) * normSq (X ω - Y ω))
    (fun ω => lemmaC_pt hn hm (X ω) (Y ω)) (hXY.const_mul _)
  have hi : Integrable f ((mlpGauss n m 1).prod P) := step.1.swap
  refine ⟨hi, ?_⟩
  rw [← integral_prod_swap f, ← integral_const_mul]
  exact step.2

/-- **Lemma C, the coupling form**: `E_F (E_ω (F(X) − F(Y)))² ≤ (2/n)·E|X − Y|²`. -/
theorem lemmaC149 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) {X Y : Ω → Fin n → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hXY : Integrable (fun ω => normSq (X ω - Y ω)) P) :
    Integrable (fun F : MlpParam n m 1 =>
        (∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) ^ 2) (mlpGauss n m 1) ∧
    ∫ F, (∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) ^ 2 ∂mlpGauss n m 1 ≤
      2 / (n : ℝ) * ∫ ω, normSq (X ω - Y ω) ∂P := by
  obtain ⟨hi, hle⟩ := lemmaC_prod P hn hm hX hY hXY
  have hDm := measurable_evalDiff (m := m) hX hY
  have hsec : ∀ᵐ F ∂mlpGauss n m 1,
      Integrable (fun ω => (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ^ 2) P := hi.prod_right_ae
  have hJ : ∀ᵐ F ∂mlpGauss n m 1,
      (∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) ^ 2 ≤
        ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ^ 2 ∂P :=
    hsec.mono fun F hF => sq_integral_le hF
  have hI2 : Integrable (fun F : MlpParam n m 1 =>
      ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ^ 2 ∂P) (mlpGauss n m 1) :=
    hi.integral_prod_left
  have hsm : StronglyMeasurable (fun F : MlpParam n m 1 =>
      ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) :=
    hDm.stronglyMeasurable.integral_prod_right'
  have hG : Integrable (fun F : MlpParam n m 1 =>
      (∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) ^ 2) (mlpGauss n m 1) := by
    refine hI2.mono' (hsm.measurable.pow_const 2).aestronglyMeasurable (hJ.mono fun F hF => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hF
  refine ⟨hG, ?_⟩
  calc ∫ F, (∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ∂P) ^ 2 ∂mlpGauss n m 1
      ≤ ∫ F, ∫ ω, (mlpEval F (X ω) 0 - mlpEval F (Y ω) 0) ^ 2 ∂P ∂mlpGauss n m 1 :=
        integral_mono_ae hG hI2 hJ
    _ = ∫ p, (mlpEval p.1 (X p.2) 0 - mlpEval p.1 (Y p.2) 0) ^ 2 ∂((mlpGauss n m 1).prod P) :=
        (integral_prod _ hi).symm
    _ ≤ _ := hle

/-! ## A Gaussian perturbation of the input -/

lemma stdGauss_normSq (n : ℕ) :
    Integrable (fun ξ : Fin n → ℝ => normSq ξ) (stdGauss (Fin n)) ∧
    ∫ ξ, normSq ξ ∂stdGauss (Fin n) = n := by
  unfold stdGauss normSq
  refine ⟨pi_sum_integrable (integrable_pow_gauss 2), ?_⟩
  rw [pi_sum (integrable_pow_gauss 2), gaussMom_eq, Fintype.card_fin]
  norm_num [gaussMom]

/-- **Lemma C for a Gaussian perturbation**: `E_{F, ξ} (F(a + sξ) − F(a))² ≤ 2s²`. -/
theorem lemmaC_gauss {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (a : Fin n → ℝ) (s : ℝ) :
    Integrable (fun p : MlpParam n m 1 × (Fin n → ℝ) =>
        (mlpEval p.1 (a + s • p.2) 0 - mlpEval p.1 a 0) ^ 2)
        ((mlpGauss n m 1).prod (stdGauss (Fin n))) ∧
    ∫ p, (mlpEval p.1 (a + s • p.2) 0 - mlpEval p.1 a 0) ^ 2
        ∂((mlpGauss n m 1).prod (stdGauss (Fin n))) ≤ 2 * s ^ 2 := by
  have e : ∀ ξ : Fin n → ℝ, normSq (a + s • ξ - a) = s ^ 2 * normSq ξ := by
    intro ξ
    rw [add_sub_cancel_left, normSq_smul]
  have hXY : Integrable (fun ξ : Fin n → ℝ => normSq (a + s • ξ - a)) (stdGauss (Fin n)) := by
    simp_rw [e]
    exact (stdGauss_normSq n).1.const_mul _
  have h := lemmaC_prod (stdGauss (Fin n)) (m := m) hn hm
    (X := fun ξ => a + s • ξ) (Y := fun _ => a)
    (measurable_const.add (measurable_const_smul s)) measurable_const hXY
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  simp_rw [e]
  rw [integral_const_mul, (stdGauss_normSq n).2]
  have hn' : (n : ℝ) ≠ 0 := by positivity
  field_simp

end BstLean.Part149

open BstLean.Part149 in
#print axioms layer_lip
open BstLean.Part149 in
#print axioms lemmaC_pt
open BstLean.Part149 in
#print axioms lemmaC_prod
open BstLean.Part149 in
#print axioms lemmaC149
open BstLean.Part149 in
#print axioms lemmaC_gauss
