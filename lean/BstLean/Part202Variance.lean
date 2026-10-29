import BstLean.Part202Quadratic

/-! ReLU input variance after integration of the whole Gaussian row. -/
namespace BstLean.Part202
open MeasureTheory ProbabilityTheory Real Filter Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170
open BstLean.Part184 (rowG rowE rowV)

lemma measurable_dot {X : Type*} [MeasurableSpace X] {d : ℕ}
    {f g : X → Fin d → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x ⬝ᵥ g x) :=
  (continuous_fst.dotProduct continuous_snd).measurable.comp (hf.prodMk hg)

section
variable {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]
variable {d : ℕ} {a : V → Fin d → ℝ}

/-- The variance is over the input distribution, at one whole Gaussian row. -/
noncomputable def wholeVariance (μ : Measure V) (a : V → Fin d → ℝ)
    (z : Fin d → ℝ) : ℝ := rowV μ (fun _ => 0) a 1 z

/-- The trace of the input covariance, with the original input distribution. -/
noncomputable def covarianceTrace (μ : Measure V) (a : V → Fin d → ℝ) : ℝ :=
  BstLean.Part151.TR μ a (fun _ => vmean μ a)

lemma covarianceTrace_nonneg : 0 ≤ covarianceTrace μ a :=
  BstLean.Part151.TR_nonneg _ _ _

lemma centred_norm_integrable (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) :
    Integrable (fun v => normSq (a v - vmean μ a)) μ :=
  int_comp_bdd ha hK (continuous_normSq.comp (continuous_id.sub continuous_const))

lemma wholeVariance_nonneg (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (z : Fin d → ℝ) : 0 ≤ wholeVariance μ a z :=
  BstLean.Part184.rowV_nonneg measurable_const ha (by simp : ∀ v : V, |(0 : ℝ)| ≤ 0) hK 1 z

lemma measurable_wholeVariance (ha : Measurable a) : Measurable (wholeVariance μ a) :=
  BstLean.Part184.measurable_rowV measurable_const ha 1

/-- Centring followed by ReLU is bounded by the input quadratic form. -/
lemma wholeVariance_le_quadratic (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (z : Fin d → ℝ) :
    wholeVariance μ a z ≤ BstLean.Part151.QR μ a (fun _ => vmean μ a) z := by
  have h := BstLean.Part184.rowV_le_var (μ := μ) measurable_const ha
    (by simp : ∀ v : V, |(0 : ℝ)| ≤ 0) hK 1 z
  simpa [wholeVariance, rowG, BstLean.Part151.QR, dotProduct_sub, int_dot ha hK] using h

/-- Variance is bounded by squared distance from the ReLU value at the input mean. -/
lemma wholeVariance_le_difference (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (z : Fin d → ℝ) :
    wholeVariance μ a z ≤
      ∫ v, (relu (z ⬝ᵥ a v) - relu (z ⬝ᵥ vmean μ a)) ^ 2 ∂μ := by
  have i1 : Integrable (fun v => relu (z ⬝ᵥ a v)) μ :=
    int_comp_bdd ha hK (continuous_relu.comp (continuous_const.dotProduct continuous_id))
  have i2 : Integrable (fun v => relu (z ⬝ᵥ a v) ^ 2) μ :=
    int_comp_bdd ha hK ((continuous_relu.comp (continuous_const.dotProduct continuous_id)).pow 2)
  let b := relu (z ⬝ᵥ vmean μ a)
  have he : (fun v => (relu (z ⬝ᵥ a v) - b) ^ 2) =
      fun v => relu (z ⬝ᵥ a v) ^ 2 - 2 * b * relu (z ⬝ᵥ a v) + b ^ 2 := by
    funext v; ring
  rw [he, integral_add (f := fun v => relu (z ⬝ᵥ a v) ^ 2 - 2 * b * relu (z ⬝ᵥ a v))
      (g := fun _ => b ^ 2) (i2.sub (i1.const_mul _)) (integrable_const _),
    integral_sub (f := fun v => relu (z ⬝ᵥ a v) ^ 2)
      (g := fun v => 2 * b * relu (z ⬝ᵥ a v)) i2 (i1.const_mul _), integral_const_mul]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    smul_eq_mul, one_mul]
  unfold wholeVariance rowV rowG
  simp only [Real.sqrt_one, one_mul, zero_add]
  nlinarith [sq_nonneg ((∫ v, relu (z ⬝ᵥ a v) ∂μ) - b)]

/-- Integration over the complete Gaussian row gives half the covariance trace. -/
theorem wholeVariance_mean (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) :
    ∫⁻ z, ENNReal.ofReal (wholeVariance μ a z) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (covarianceTrace μ a / 2) := by
  have iT := centred_norm_integrable (μ := μ) ha hK
  have hr : ∀ z, Integrable
      (fun v => (relu (z ⬝ᵥ a v) - relu (z ⬝ᵥ vmean μ a)) ^ 2) μ :=
    fun z => BstLean.Part151.rdiff_int ha measurable_const iT z
  have hj : Measurable (fun p : (Fin d → ℝ) × V => ENNReal.ofReal
      ((relu (p.1 ⬝ᵥ a p.2) - relu (p.1 ⬝ᵥ vmean μ a)) ^ 2)) := by
    apply ENNReal.measurable_ofReal.comp
    exact ((measurable_relu.comp (measurable_dot measurable_fst (ha.comp measurable_snd))).sub
      (measurable_relu.comp (measurable_dot measurable_fst measurable_const))).pow_const 2
  calc ∫⁻ z, ENNReal.ofReal (wholeVariance μ a z) ∂stdGauss (Fin d)
      ≤ ∫⁻ z, ∫⁻ v, ENNReal.ofReal
          ((relu (z ⬝ᵥ a v) - relu (z ⬝ᵥ vmean μ a)) ^ 2) ∂μ ∂stdGauss (Fin d) := by
        refine lintegral_mono fun z => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hr z)
          (Eventually.of_forall fun v => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (wholeVariance_le_difference ha hK z)
    _ = ∫⁻ v, ∫⁻ z, ENNReal.ofReal
          ((relu (z ⬝ᵥ a v) - relu (z ⬝ᵥ vmean μ a)) ^ 2) ∂stdGauss (Fin d) ∂μ :=
        lintegral_lintegral_swap hj.aemeasurable
    _ ≤ ∫⁻ v, ENNReal.ofReal (1 / 2 * normSq (a v - vmean μ a)) ∂μ := by
        refine lintegral_mono fun v => ?_
        simpa only [Real.sqrt_one, one_smul] using
          BstLean.Part151.lemmaR_ii (by norm_num : (0 : ℝ) ≤ 1) (a v) (vmean μ a)
    _ = ENNReal.ofReal (covarianceTrace μ a / 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (iT.const_mul _)
          (Eventually.of_forall fun v => mul_nonneg (by norm_num) (normSq_nonneg _)),
          integral_const_mul]
        congr 1
        unfold covarianceTrace BstLean.Part151.TR
        ring

/-- Every whole-row variance moment has a trace majorant. -/
theorem wholeVariance_moment (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ z, ENNReal.ofReal (wholeVariance μ a z ^ p) ∂stdGauss (Fin d) ≤
      ENNReal.ofReal (BstLean.Part29.gaussMom (2 * p) * covarianceTrace μ a ^ p) := by
  refine (lintegral_mono fun z => ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (wholeVariance_nonneg ha hK z)
      (wholeVariance_le_quadratic ha hK z) p)).trans ?_
  exact quadratic_moment ha measurable_const (centred_norm_integrable ha hK) hp

end
end BstLean.Part202
