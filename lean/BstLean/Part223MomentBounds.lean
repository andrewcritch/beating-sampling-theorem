import BstLean.Part223Mixed
import BstLean.Part220Norm

/-! Moment bounds on a measure of mass at most one. -/
namespace BstLean.Part223
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure MomentBound (μ : Measure X) (k : ℕ) (f : X → ℝ) (B : ℝ) : Prop where
  measurable : Measurable f
  nonneg : 0 ≤ B
  moment : ∫⁻ x, ENNReal.ofReal (|f x| ^ k) ∂μ ≤ ENNReal.ofReal (B ^ k)

lemma MomentBound.add {k : ℕ} (hk : 1 ≤ k) {f g : X → ℝ} {A B : ℝ}
    (hf : MomentBound μ k f A) (hg : MomentBound μ k g B) :
    MomentBound μ k (fun x => f x + g x) (A + B) :=
  ⟨hf.measurable.add hg.measurable, add_nonneg hf.nonneg hg.nonneg,
    BstLean.Part213.moment_minkowski hf.measurable hg.measurable hk hf.nonneg hg.nonneg
      hf.moment hg.moment⟩

lemma MomentBound.scale {k : ℕ} {f : X → ℝ} {B a : ℝ}
    (hf : MomentBound μ k f B) (ha : 0 ≤ a) :
    MomentBound μ k (fun x => a * f x) (a * B) := by
  refine ⟨hf.measurable.const_mul a, mul_nonneg ha hf.nonneg, ?_⟩
  simp only [abs_mul, abs_of_nonneg ha, mul_pow, ENNReal.ofReal_mul (pow_nonneg ha _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl hf.moment

lemma MomentBound.mono {k : ℕ} {f g : X → ℝ} {B : ℝ}
    (hf : MomentBound μ k f B) (hg : Measurable g)
    (hle : ∀ x, |g x| ≤ |f x|) : MomentBound μ k g B := by
  refine ⟨hg, hf.nonneg, ?_⟩
  exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (abs_nonneg _) (hle x) k)).trans hf.moment

lemma MomentBound.power {k r : ℕ} {f : X → ℝ} {B : ℝ}
    (hf : MomentBound μ (k * r) f B) :
    MomentBound μ k (fun x => f x ^ r) (B ^ r) := by
  refine ⟨hf.measurable.pow_const r, pow_nonneg hf.nonneg r, ?_⟩
  simpa only [abs_pow, ← pow_mul, Nat.mul_comm r k] using hf.moment

lemma MomentBound.sqrt {k : ℕ} {f : X → ℝ} {B : ℝ}
    (hf : MomentBound μ k f B) (h0 : ∀ x, 0 ≤ f x) :
    MomentBound μ (2 * k) (fun x => sqrt (f x)) (sqrt B) := by
  refine ⟨hf.measurable.sqrt, sqrt_nonneg _, ?_⟩
  simpa only [abs_of_nonneg (sqrt_nonneg _), pow_mul, sq_sqrt (h0 _),
    sq_sqrt hf.nonneg, abs_of_nonneg (h0 _)] using hf.moment

lemma MomentBound.lower {k l : ℕ} (hk : 1 ≤ k) (hkl : k ≤ l)
    (hmass : μ univ ≤ 1) {f : X → ℝ} {B : ℝ}
    (hf : MomentBound μ l f B) : MomentBound μ k f B := by
  have hk0 : k ≠ 0 := by omega
  have hl0 : l ≠ 0 := by omega
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := f)
    (show (k : ℝ≥0∞) ≤ l by exact_mod_cast hkl) hf.measurable.aestronglyMeasurable
  have he : 0 ≤ 1 / (k : ℝ≥0∞).toReal - 1 / (l : ℝ≥0∞).toReal := by
    simp only [ENNReal.toReal_natCast]
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by exact_mod_cast (by omega : 0 < k))
      (by exact_mod_cast hkl)
  have hm : μ univ ^ (1 / (k : ℝ≥0∞).toReal - 1 / (l : ℝ≥0∞).toReal) ≤ 1 := by
    simpa only [ENNReal.one_rpow] using ENNReal.rpow_le_rpow hmass he
  have hn : eLpNorm f (k : ℝ≥0∞) μ ≤ ENNReal.ofReal B := by
    refine hc.trans ((mul_le_mul' (BstLean.Part213.moment_norm_bound hf.measurable
      hl0 hf.nonneg hf.moment) hm).trans ?_)
    simp
  have h := pow_le_pow_left' hn k
  rw [BstLean.Part153.eLpNorm_nat_pow hk0 hf.measurable.aestronglyMeasurable,
    ← ENNReal.ofReal_pow hf.nonneg] at h
  exact ⟨hf.measurable, hf.nonneg, h⟩

lemma MomentBound.mul16 {f g : X → ℝ} {A B : ℝ}
    (hf : MomentBound μ 32 f A) (hg : MomentBound μ 32 g B) :
    MomentBound μ 16 (fun x => f x * g x) (A * B) := by
  haveI : ENNReal.HolderTriple (32 : ℝ≥0∞) 32 16 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := (32 : ℝ≥0∞))
    (q := (32 : ℝ≥0∞)) (r := (16 : ℝ≥0∞))
      hf.measurable.aestronglyMeasurable hg.measurable.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 16 μ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hf.nonneg]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf.measurable
      (by norm_num) hf.nonneg hf.moment)
      (BstLean.Part213.moment_norm_bound hg.measurable (by norm_num) hg.nonneg hg.moment)
  have hp := pow_le_pow_left' hn 16
  have he : eLpNorm (fun x => f x * g x) (16 : ℝ≥0∞) μ ^ (16 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 16) ∂μ := by
    exact BstLean.Part153.eLpNorm_nat_pow (μ := μ) (f := fun x => f x * g x)
      (by norm_num : (16 : ℕ) ≠ 0) (hf.measurable.mul hg.measurable).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hf.nonneg hg.nonneg)] at hp
  exact ⟨hf.measurable.mul hg.measurable, mul_nonneg hf.nonneg hg.nonneg, hp⟩

lemma MomentBound.mul8 {f g : X → ℝ} {A B : ℝ}
    (hf : MomentBound μ 16 f A) (hg : MomentBound μ 16 g B) :
    MomentBound μ 8 (fun x => f x * g x) (A * B) := by
  haveI : ENNReal.HolderTriple (16 : ℝ≥0∞) 16 8 := by
    constructor
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp
    norm_num [ENNReal.toReal_add]
  have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := (16 : ℝ≥0∞))
    (q := (16 : ℝ≥0∞)) (r := (8 : ℝ≥0∞))
      hf.measurable.aestronglyMeasurable hg.measurable.aestronglyMeasurable
  have hn : eLpNorm (fun x => f x * g x) 8 μ ≤ ENNReal.ofReal (A * B) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul hf.nonneg]
    exact mul_le_mul' (BstLean.Part213.moment_norm_bound hf.measurable
      (by norm_num) hf.nonneg hf.moment)
      (BstLean.Part213.moment_norm_bound hg.measurable (by norm_num) hg.nonneg hg.moment)
  have hp := pow_le_pow_left' hn 8
  have he : eLpNorm (fun x => f x * g x) (8 : ℝ≥0∞) μ ^ (8 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (|f x * g x| ^ 8) ∂μ := by
    exact BstLean.Part153.eLpNorm_nat_pow (μ := μ) (f := fun x => f x * g x)
      (by norm_num : (8 : ℕ) ≠ 0) (hf.measurable.mul hg.measurable).aestronglyMeasurable
  rw [he, ← ENNReal.ofReal_pow (mul_nonneg hf.nonneg hg.nonneg)] at hp
  exact ⟨hf.measurable.mul hg.measurable, mul_nonneg hf.nonneg hg.nonneg, hp⟩

#print axioms MomentBound.lower
#print axioms MomentBound.mul16
end BstLean.Part223
