import BstLean.Part220Norm

/-! The order-four latitude norm retains the order64 first-layer payment. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

variable {X V G : Type*} [MeasurableSpace X] [MeasurableSpace V] [MeasurableSpace G]

/-- This is the sixty-fourth power of the order-four latitude norm. -/
noncomputable def latitudeStatistic64 (μ : Measure V) (f : V → ℝ) : ℝ≥0∞ :=
  (∫⁻ v, ENNReal.ofReal (|f v| ^ 4) ∂μ) ^ 16

theorem latitudeStatistic64_eq (μ : Measure V) {f : V → ℝ} (hf : Measurable f) :
    latitudeStatistic64 μ f = eLpNorm f 4 μ ^ (64 : ℕ) := by
  rw [latitudeStatistic64, ← BstLean.Part153.eLpNorm_nat_pow
    (by norm_num : (4 : ℕ) ≠ 0) hf.aestronglyMeasurable, ← pow_mul]
  norm_num

/-- Jensen on the latitude distribution precedes the first-layer integration. -/
theorem latitudeStatistic64_le (μ : Measure V) [IsProbabilityMeasure μ]
    {f : V → ℝ} (hf : Measurable f) :
    latitudeStatistic64 μ f ≤ ∫⁻ v, ENNReal.ofReal (|f v| ^ 64) ∂μ := by
  rw [latitudeStatistic64_eq μ hf,
    ← BstLean.Part153.eLpNorm_nat_pow (by norm_num : (64 : ℕ) ≠ 0)
      hf.aestronglyMeasurable]
  exact pow_le_pow_left' (eLpNorm_le_eLpNorm_of_exponent_le
    (by norm_num : (4 : ℝ≥0∞) ≤ 64)) 64

/-- Two order128 bounds supply the order64 bound of their product.
The two fields can depend on the same first-layer matrix. -/
theorem product_moment64 (σ : Measure X) {f g : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ∫⁻ x, ENNReal.ofReal (|f x| ^ 128) ∂σ ≤ ENNReal.ofReal (A ^ 128))
    (hG : ∫⁻ x, ENNReal.ofReal (|g x| ^ 128) ∂σ ≤ ENNReal.ofReal (B ^ 128)) :
    ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 64) ∂σ ≤ ENNReal.ofReal ((A * B) ^ 64) := by
  haveI : ENNReal.HolderTriple (128 : ℝ≥0∞) 128 64 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := σ) (p := (128 : ℝ≥0∞))
    (q := (128 : ℝ≥0∞)) (r := (64 : ℝ≥0∞)) hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 64 σ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hA]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf (by norm_num) hA hF)
      (BstLean.Part213.moment_norm_bound hg (by norm_num) hB hG)
  have hp := pow_le_pow_left' hn 64
  have he : eLpNorm (fun x => f x * g x) (64 : ℝ≥0∞) σ ^ (64 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 64) ∂σ := by
    simpa using BstLean.Part153.eLpNorm_nat_pow (μ := σ) (f := fun x => f x * g x)
      (by norm_num : (64 : ℕ) ≠ 0) (hf.mul hg).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hA hB)] at hp
  exact hp

/-- Mixed latitude and first-layer integration needs no independence across latitudes. -/
theorem latitudeStatistic64_moment (σ : Measure X) [SFinite σ]
    (μ : Measure V) [IsProbabilityMeasure μ] {f : X → V → ℝ}
    (hf : Measurable (Function.uncurry f)) {B : ℝ}
    (hM : ∀ᵐ v ∂μ, ∫⁻ x, ENNReal.ofReal (|f x v| ^ 64) ∂σ ≤ ENNReal.ofReal (B ^ 64)) :
    ∫⁻ x, latitudeStatistic64 μ (f x) ∂σ ≤ ENNReal.ofReal (B ^ 64) := by
  calc
    _ ≤ ∫⁻ x, ∫⁻ v, ENNReal.ofReal (|f x v| ^ 64) ∂μ ∂σ := by
      exact lintegral_mono fun x => latitudeStatistic64_le μ
        (hf.comp (measurable_const.prodMk measurable_id))
    _ = ∫⁻ v, ∫⁻ x, ENNReal.ofReal (|f x v| ^ 64) ∂σ ∂μ :=
      lintegral_lintegral_swap (hf.abs.pow_const 64 |>.ennreal_ofReal).aemeasurable
    _ ≤ ∫⁻ _v, ENNReal.ofReal (B ^ 64) ∂μ := lintegral_mono_ae hM
    _ = _ := by simp

#print axioms latitudeStatistic64_le
#print axioms product_moment64
#print axioms latitudeStatistic64_moment
end BstLean.Part223
