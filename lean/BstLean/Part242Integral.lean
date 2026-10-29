import BstLean.Part242Holder

/-! The weighted location price uses one reciprocal moment on the kept measure. -/
namespace BstLean.Part242
open MeasureTheory Real Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma LBound.nonnegIntegral {k : ℕ} (hk : k ≠ 0) {f : X → ℝ} {B : ℝ}
    (hf : LBound μ k f B) (h0 : ∀ x, 0 ≤ f x) :
    Integrable (fun x => f x ^ k) μ ∧ ∫ x, f x ^ k ∂μ ≤ B ^ k := by
  have h := hf.toMoment hk
  have hi : HasFiniteIntegral (fun x => f x ^ k) μ := by
    unfold HasFiniteIntegral
    simpa only [Real.enorm_eq_ofReal (pow_nonneg (h0 _) k), abs_of_nonneg (h0 _)] using
      h.moment.trans_lt ENNReal.ofReal_lt_top
  have ii : Integrable (fun x => f x ^ k) μ :=
    ⟨(hf.measurable.pow_const k).aestronglyMeasurable, hi⟩
  refine ⟨ii, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => pow_nonneg (h0 x) k)
    (hf.measurable.pow_const k).aestronglyMeasurable]
  simpa only [abs_of_nonneg (h0 _), ENNReal.toReal_ofReal (pow_nonneg hf.nonneg k)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h.moment

lemma LBound.evenIntegral {k : ℕ} (hk : k ≠ 0) (he : Even k)
    {f : X → ℝ} {B : ℝ} (hf : LBound μ k f B) :
    Integrable (fun x => f x ^ k) μ ∧ ∫ x, f x ^ k ∂μ ≤ B ^ k := by
  have h := hf.toMoment hk
  have hi : HasFiniteIntegral (fun x => f x ^ k) μ := by
    unfold HasFiniteIntegral
    simpa only [Real.enorm_eq_ofReal (he.pow_nonneg _), he.pow_abs] using
      h.moment.trans_lt ENNReal.ofReal_lt_top
  have ii : Integrable (fun x => f x ^ k) μ :=
    ⟨(hf.measurable.pow_const k).aestronglyMeasurable, hi⟩
  refine ⟨ii, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => he.pow_nonneg (f x))
    (hf.measurable.pow_const k).aestronglyMeasurable]
  simpa only [he.pow_abs, ENNReal.toReal_ofReal (pow_nonneg hf.nonneg k)] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h.moment

lemma LBound.integralAbs {f : X → ℝ} {B : ℝ} (hf : LBound μ 1 f B) :
    Integrable f μ ∧ ∫ x, |f x| ∂μ ≤ B := by
  have hi : Integrable f μ := memLp_one_iff_integrable.mp
    (hf.bound.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  have he : ENNReal.ofReal (∫ x, |f x| ∂μ) = eLpNorm f 1 μ := by
    simpa only [Real.norm_eq_abs] using
      (ofReal_integral_norm_eq_lintegral_enorm hi).trans
        (eLpNorm_one_eq_lintegral_enorm hf.measurable.aestronglyMeasurable).symm
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (he ▸ hf.bound)
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun x => abs_nonneg _),
    ENNReal.toReal_ofReal hf.nonneg] using h

theorem SY_location_integral (hmass : μ univ ≤ 1)
    {df Y : X → ℝ} {af Γ : ℝ}
    (hd : LBound μ 8 df af) (hR : LBound μ 4 (fun x => 1 / Y x) Γ)
    (hY : ∀ᵐ x ∂μ, 0 < Y x) :
    Integrable (fun x => df x ^ 2 / Y x) μ ∧
      ∫ x, df x ^ 2 / Y x ∂μ ≤ af ^ 2 * Γ := by
  have hsq : LBound μ 4 (fun x => df x ^ 2) (af ^ 2) := by
    simpa only [Nat.cast_ofNat] using LBound.ofMoment (by norm_num : (4 : ℕ) ≠ 0)
      ((hd.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 4) (r := 2))
  have hr : LBound μ (4 / 3) (fun x => 1 / Y x) Γ :=
    hR.lower fourthirds_ne_zero (by norm_num) fourthirds_le_four hmass
  have h := (hsq.mul hr).integralAbs
  have he : (fun x => df x ^ 2 / Y x) = fun x => df x ^ 2 * (1 / Y x) := by
    funext x
    ring
  rw [he]
  refine ⟨h.1, ?_⟩
  have hp : ∀ᵐ x ∂μ, |df x ^ 2 * (1 / Y x)| = df x ^ 2 * (1 / Y x) :=
    hY.mono fun x hx => abs_of_nonneg (by positivity)
  rw [integral_congr_ae hp] at h
  exact h.2

end BstLean.Part242
