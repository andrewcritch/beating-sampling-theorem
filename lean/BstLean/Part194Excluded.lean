import BstLean.Part194Lip

/-! The exceptional first-moment allowance stays inside the input expectation. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part154

theorem excluded_first_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {σ η : Ω → ℝ} {a b p q : ℝ}
    (hi : Integrable σ μ) (hσm : Measurable σ) (hηm : Measurable η)
    (hσ0 : ∀ x, 0 ≤ σ x) (hle : ∀ x, σ x ≤ η x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : μ.real {x | σ x < a} ≤ p) (hq : μ.real {x | η x < b} ≤ q) :
    (∫ x in {x | σ x < a} ∪ {x | η x < b}, σ x ∂μ) ≤ a * p + b * q := by
  classical
  let S : Set Ω := {x | σ x < a}
  let F : Set Ω := {x | η x < b}
  have hS : MeasurableSet S := measurableSet_lt hσm measurable_const
  have hF : MeasurableSet F := measurableSet_lt hηm measurable_const
  have hU : MeasurableSet (S ∪ F) := hS.union hF
  have hSI : Integrable (S.indicator σ) μ := hi.indicator hS
  have hFI : Integrable (F.indicator σ) μ := hi.indicator hF
  have hUI : Integrable ((S ∪ F).indicator σ) μ := hi.indicator hU
  have hleS : (∫ x in S, σ x ∂μ) ≤ a * p := by
    have h := setIntegral_mono_on hi.integrableOn (integrable_const a).integrableOn hS
      (fun x hx => (show σ x < a from hx).le)
    rw [setIntegral_const, smul_eq_mul] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hp ha])
  have hleF : (∫ x in F, σ x ∂μ) ≤ b * q := by
    have h := setIntegral_mono_on hi.integrableOn (integrable_const b).integrableOn hF
      (fun x hx => (hle x).trans (show η x < b from hx).le)
    rw [setIntegral_const, smul_eq_mul] at h
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hq hb])
  have hPoint : ∀ x, (S ∪ F).indicator σ x ≤ S.indicator σ x + F.indicator σ x := by
    intro x
    by_cases hxS : x ∈ S <;> by_cases hxF : x ∈ F <;>
      simp [hxS, hxF, hσ0 x]
  have h := integral_mono hUI (hSI.add hFI) hPoint
  simp only [Pi.add_apply] at h
  rw [integral_add hSI hFI, integral_indicator hS, integral_indicator hF,
    integral_indicator hU] at h
  exact h.trans (add_le_add hleS hleF)

/-- The displayed MF exceptional allowance follows from the two supplied tails. -/
theorem MF_excluded_sigma {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg k k3 p q : ℝ} (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hk : 0 < k) (hk3 : 0 < k3)
    (hp : (stdGauss (Fin d)).real {x | sig2F (stdGauss (Fin d)) f x <
      sF2 (stdGauss (Fin d)) f / k} ≤ p)
    (hq : (stdGauss (Fin d)).real {x | normSq (f x) <
      GamF (stdGauss (Fin d)) f / k3} ≤ q) :
    (∫ x in {x | sig2F (stdGauss (Fin d)) f x < sF2 (stdGauss (Fin d)) f / k} ∪
      {x | normSq (f x) < GamF (stdGauss (Fin d)) f / k3},
      √(sig2F (stdGauss (Fin d)) f x) ∂stdGauss (Fin d)) ≤
        sF (stdGauss (Fin d)) f / √k * p + √(GamF (stdGauss (Fin d)) f) / √k3 * q := by
  have hG : 0 < GamF (stdGauss (Fin d)) f := by
    have hs := H.hs; unfold sF2 at hs; linarith [H.hbar]
  have hEqS : {x | √(sig2F (stdGauss (Fin d)) f x) <
      sF (stdGauss (Fin d)) f / √k} =
      {x | sig2F (stdGauss (Fin d)) f x < sF2 (stdGauss (Fin d)) f / k} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, sF, ← sqrt_div H.hs.le]
    exact sqrt_lt_sqrt_iff (sig2F_nonneg _ _ _)
  have hEqF : {x | √(normSq (f x)) < √(GamF (stdGauss (Fin d)) f) / √k3} =
      {x | normSq (f x) < GamF (stdGauss (Fin d)) f / k3} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq, ← sqrt_div hG.le]
    exact sqrt_lt_sqrt_iff (BstLean.Part130.normSq_nonneg _)
  have ht := excluded_first_moment (η := fun x => √(normSq (f x)))
    H.sig_int.1 H.meas_sig.sqrt
    ((BstLean.Part130.measurable_normSq.comp H.hf).sqrt)
    (fun _ => sqrt_nonneg _) (fun x => sqrt_le_sqrt (H.sig_le x))
    (div_nonneg H.sF_pos.1.le (sqrt_nonneg _) : 0 ≤ sF (stdGauss (Fin d)) f / √k)
    (by positivity : 0 ≤ √(GamF (stdGauss (Fin d)) f) / √k3)
    (hEqS ▸ hp) (hEqF ▸ hq)
  rwa [hEqS, hEqF] at ht

#print axioms excluded_first_moment
#print axioms MF_excluded_sigma
end BstLean.Part194
