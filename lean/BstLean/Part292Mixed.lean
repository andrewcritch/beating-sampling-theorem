import BstLean.Part220Norm

/-! The order-four latitude norm retains the order416 first-layer payment. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {X V G : Type*} [MeasurableSpace X] [MeasurableSpace V] [MeasurableSpace G]

/-- This is the four-hundred-sixteenth power of the order-four latitude norm. -/
noncomputable def latitudeStatistic416 (μ : Measure V) (f : V → ℝ) : ℝ≥0∞ :=
  (∫⁻ v, ENNReal.ofReal (|f v| ^ 4) ∂μ) ^ 104

theorem latitudeStatistic416_eq (μ : Measure V) {f : V → ℝ} (hf : Measurable f) :
    latitudeStatistic416 μ f = eLpNorm f 4 μ ^ (416 : ℕ) := by
  rw [latitudeStatistic416, ← BstLean.Part153.eLpNorm_nat_pow
    (by norm_num : (4 : ℕ) ≠ 0) hf.aestronglyMeasurable, ← pow_mul]
  norm_num

/-- Jensen on the latitude distribution precedes the first-layer integration. -/
theorem latitudeStatistic416_le (μ : Measure V) [IsProbabilityMeasure μ]
    {f : V → ℝ} (hf : Measurable f) :
    latitudeStatistic416 μ f ≤ ∫⁻ v, ENNReal.ofReal (|f v| ^ 416) ∂μ := by
  rw [latitudeStatistic416_eq μ hf,
    ← BstLean.Part153.eLpNorm_nat_pow (by norm_num : (416 : ℕ) ≠ 0)
      hf.aestronglyMeasurable]
  exact pow_le_pow_left' (eLpNorm_le_eLpNorm_of_exponent_le
    (by norm_num : (4 : ℝ≥0∞) ≤ 416)) 416

/-- Two order832 bounds supply the order416 bound of their product.
The two fields can depend on the same first-layer matrix. -/
theorem product_moment416 (σ : Measure X) {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∫⁻ x, ENNReal.ofReal (|f x| ^ 832) ∂σ ≤ ENNReal.ofReal (A ^ 832))
    (hG : ∫⁻ x, ENNReal.ofReal (|g x| ^ 832) ∂σ ≤ ENNReal.ofReal (B ^ 832)) :
    ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 416) ∂σ ≤ ENNReal.ofReal ((A * B) ^ 416) := by
  haveI : ENNReal.HolderTriple (832 : ℝ≥0∞) 832 416 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := σ) (p := (832 : ℝ≥0∞))
    (q := (832 : ℝ≥0∞)) (r := (416 : ℝ≥0∞)) hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 416 σ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hA]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf (by norm_num) hA hF)
      (BstLean.Part213.moment_norm_bound hg (by norm_num) hB hG)
  have hp := pow_le_pow_left' hn 416
  have he : eLpNorm (fun x => f x * g x) (416 : ℝ≥0∞) σ ^ (416 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 416) ∂σ := by
    simpa using BstLean.Part153.eLpNorm_nat_pow (μ := σ) (f := fun x => f x * g x)
      (by norm_num : (416 : ℕ) ≠ 0) (hf.mul hg).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hA hB)] at hp
  exact hp

/-- Mixed latitude and first-layer integration needs no independence across latitudes. -/
theorem latitudeStatistic416_moment (σ : Measure X) [SFinite σ]
    (μ : Measure V) [IsProbabilityMeasure μ] {f : X → V → ℝ}
    (hf : Measurable (Function.uncurry f)) {B : ℝ}
    (hM : ∀ᵐ v ∂μ, ∫⁻ x, ENNReal.ofReal (|f x v| ^ 416) ∂σ ≤ ENNReal.ofReal (B ^ 416)) :
    ∫⁻ x, latitudeStatistic416 μ (f x) ∂σ ≤ ENNReal.ofReal (B ^ 416) := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ v, ENNReal.ofReal (|f x v| ^ 416) ∂μ ∂σ := by
      exact lintegral_mono fun x => latitudeStatistic416_le μ
        (hf.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ v, ∫⁻ x, ENNReal.ofReal (|f x v| ^ 416) ∂σ ∂μ :=
      lintegral_lintegral_swap (hf.abs.pow_const 416 |>.ennreal_ofReal).aemeasurable
    _ ≤ ∫⁻ _v, ENNReal.ofReal (B ^ 416) ∂μ := lintegral_mono_ae hM
    _ = _ := by simp

#print axioms latitudeStatistic416_le
#print axioms product_moment416
#print axioms latitudeStatistic416_moment
end BstLean.Part292
