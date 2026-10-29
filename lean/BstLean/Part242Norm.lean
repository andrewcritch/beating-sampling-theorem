import BstLean.Part223MomentBounds

/-! Norm bounds on the original, unnormalized distribution. -/
namespace BstLean.Part242
open MeasureTheory Real
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

structure LBound (μ : Measure X) (p : ℝ≥0∞) (f : X → ℝ) (A : ℝ) : Prop where
  measurable : Measurable f
  nonneg : 0 ≤ A
  bound : eLpNorm f p μ ≤ ENNReal.ofReal A

lemma LBound.ofMoment {k : ℕ} (hk : k ≠ 0) {f : X → ℝ} {A : ℝ}
    (h : BstLean.Part223.MomentBound μ k f A) : LBound μ k f A :=
  ⟨h.measurable, h.nonneg, BstLean.Part213.moment_norm_bound
    h.measurable hk h.nonneg h.moment⟩

lemma LBound.toMoment {k : ℕ} (hk : k ≠ 0) {f : X → ℝ} {A : ℝ}
    (h : LBound μ k f A) : BstLean.Part223.MomentBound μ k f A := by
  refine ⟨h.measurable, h.nonneg, ?_⟩
  have hp := pow_le_pow_left' h.bound k
  rw [BstLean.Part153.eLpNorm_nat_pow hk h.measurable.aestronglyMeasurable,
    ← ENNReal.ofReal_pow h.nonneg] at hp
  exact hp

lemma LBound.add {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : X → ℝ} {A B : ℝ}
    (hf : LBound μ p f A) (hg : LBound μ p g B) :
    LBound μ p (fun x => f x + g x) (A + B) := by
  refine ⟨hf.measurable.add hg.measurable, add_nonneg hf.nonneg hg.nonneg, ?_⟩
  refine (eLpNorm_add_le (f := f) (g := g) hp).trans ?_
  rw [ENNReal.ofReal_add hf.nonneg hg.nonneg]
  exact add_le_add hf.bound hg.bound

lemma LBound.mono {p : ℝ≥0∞} {f g : X → ℝ} {A : ℝ}
    (hf : LBound μ p f A) (mg : Measurable g)
    (hle : ∀ᵐ x ∂μ, |g x| ≤ |f x|) : LBound μ p g A := by
  refine ⟨mg, hf.nonneg, ?_⟩
  exact (eLpNorm_mono_ae mg.aestronglyMeasurable
    (hle.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)).trans hf.bound

lemma LBound.restrict {p : ℝ≥0∞} {f : X → ℝ} {A : ℝ}
    (hf : LBound μ p f A) (K : Set X) : LBound (μ.restrict K) p f A :=
  ⟨hf.measurable, hf.nonneg,
    (eLpNorm_mono_measure f Measure.restrict_le_self).trans hf.bound⟩

lemma LBound.lower {p q : ℝ≥0∞} (hp : p ≠ 0) (hq : q ≠ ∞)
    (hpq : p ≤ q) (hmass : μ Set.univ ≤ 1) {f : X → ℝ} {A : ℝ}
    (hf : LBound μ q f A) : LBound μ p f A := by
  have he : 0 ≤ 1 / p.toReal - 1 / q.toReal := by
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (ENNReal.toReal_pos hp (ne_top_of_le_ne_top hq hpq))
      (ENNReal.toReal_mono hq hpq)
  have hm : μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hmass he
  refine ⟨hf.measurable, hf.nonneg, ?_⟩
  exact (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf.measurable.aestronglyMeasurable).trans
    ((mul_le_mul' hf.bound hm).trans (by simp))

lemma LBound.mul {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {f g : X → ℝ} {A B : ℝ} (hf : LBound μ p f A) (hg : LBound μ q g B) :
    LBound μ r (fun x => f x * g x) (A * B) := by
  refine ⟨hf.measurable.mul hg.measurable, mul_nonneg hf.nonneg hg.nonneg, ?_⟩
  refine (eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := r)
    hf.measurable.aestronglyMeasurable
    hg.measurable.aestronglyMeasurable).trans ?_
  rw [ENNReal.ofReal_mul hf.nonneg]
  exact mul_le_mul' hf.bound hg.bound

lemma LBound.scale {k : ℕ} (hk : k ≠ 0) {f : X → ℝ} {A a : ℝ}
    (hf : LBound μ k f A) (ha : 0 ≤ a) : LBound μ k (fun x => a * f x) (a * A) :=
  LBound.ofMoment hk ((hf.toMoment hk).scale ha)

lemma LBound.const {k : ℕ} (hk : k ≠ 0) (hmass : μ Set.univ ≤ 1)
    {a : ℝ} (ha : 0 ≤ a) : LBound μ k (fun _ => a) a := by
  apply LBound.ofMoment hk
  refine ⟨measurable_const, ha, ?_⟩
  simp only [abs_of_nonneg ha, lintegral_const]
  simpa only [mul_one] using mul_le_mul_right hmass (ENNReal.ofReal (a ^ k))

lemma LBound.squareIntegral {f : X → ℝ} {A : ℝ} (hf : LBound μ 2 f A) :
    Integrable (fun x => f x ^ 2) μ ∧ ∫ x, f x ^ 2 ∂μ ≤ A ^ 2 := by
  have h := hf.toMoment (by norm_num : (2 : ℕ) ≠ 0)
  have hi : HasFiniteIntegral (fun x => f x ^ 2) μ := by
    unfold HasFiniteIntegral
    simpa only [Real.enorm_eq_ofReal (sq_nonneg _), sq_abs] using
      h.moment.trans_lt ENNReal.ofReal_lt_top
  have ii : Integrable (fun x => f x ^ 2) μ := ⟨hf.measurable.pow_const 2 |>.aestronglyMeasurable, hi⟩
  refine ⟨ii, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (hf.measurable.pow_const 2).aestronglyMeasurable]
  simpa only [sq_abs, ENNReal.toReal_ofReal (sq_nonneg A)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h.moment

end BstLean.Part242
