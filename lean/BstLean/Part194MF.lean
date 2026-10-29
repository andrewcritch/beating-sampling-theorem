import BstLean.Part194Excluded
import BstLean.Part194Pair
import BstLean.Part194Price
import BstLean.Part154K0

/-! The integrated MF remainder formula, conditional on the actual kernel bounds.
The Price covariance identity remains outside this theorem. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part153 (nrm)
open BstLean.Part154

theorem MF_integrated_remainder_of_kernel_bounds {d m : ℕ}
    {f : (Fin d → ℝ) → Fin m → ℝ} {L pg r rG k k3 : ℝ}
    (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hV : ∀ x y, nrm (f x - f y) ≤ L * nrm (x - y))
    (hr : 0 < r) (hrG : 0 < rG) (hk : 1 < k) (hk3 : 1 < k3)
    (hRatio : L ^ 2 / sF2 (stdGauss (Fin d)) f ≤ r)
    (hRatioG : L ^ 2 / GamF (stdGauss (Fin d)) f ≤ rG)
    (hRad : 0 ≤ 1 - 2 * r) (hRadG : 0 ≤ 1 - rG)
    (hgap : 0 < gap 2 r k) (hgapG : 0 < gap 1 rG k3)
    {R : (Fin d → ℝ) × (Fin d → ℝ) → ℝ}
    (hRm : AEStronglyMeasurable R ((stdGauss (Fin d)).prod (stdGauss (Fin d))))
    (hR0 : ∀ p, 0 ≤ R p)
    (hKernel : ∀ p,
      sF2 (stdGauss (Fin d)) f / k ≤ sig2F (stdGauss (Fin d)) f p.1 →
      sF2 (stdGauss (Fin d)) f / k ≤ sig2F (stdGauss (Fin d)) f p.2 →
      GamF (stdGauss (Fin d)) f / k3 ≤ normSq (f p.1) →
      GamF (stdGauss (Fin d)) f / k3 ≤ normSq (f p.2) →
      R p ≤ K0 * ccF (stdGauss (Fin d)) f p ^ 2 /
        √(sgF (stdGauss (Fin d)) f p.1 * sgF (stdGauss (Fin d)) f p.2 *
          nrm (f p.1) * nrm (f p.2)))
    (hGlobal : ∀ p, R p ≤ sgF (stdGauss (Fin d)) f p.1 *
      sgF (stdGauss (Fin d)) f p.2 / 8) :
    Integrable R ((stdGauss (Fin d)).prod (stdGauss (Fin d))) ∧
      (∫ p, R p ∂(stdGauss (Fin d)).prod (stdGauss (Fin d))) ≤
        K0 * √(k * k3) * hsF (stdGauss (Fin d)) f /
          (sF (stdGauss (Fin d)) f * √(GamF (stdGauss (Fin d)) f)) +
        sF (stdGauss (Fin d)) f / 4 *
          (sF (stdGauss (Fin d)) f * tail 2 r k / √k +
            √(GamF (stdGauss (Fin d)) f) * tail 1 rG k3 / √k3) := by
  let μ := stdGauss (Fin d)
  let B := {x | sig2F μ f x < sF2 μ f / k} ∪ {x | normSq (f x) < GamF μ f / k3}
  have hk0 : 0 < k := by linarith
  have hk30 : 0 < k3 := by linarith
  have hG : 0 < GamF μ f := by
    have hs := H.hs; unfold sF2 at hs; linarith [H.hbar]
  have hs0 : 0 < sF μ f := H.sF_pos.1
  have ha : 0 < sF μ f / √k := by positivity
  have hb : 0 < √(GamF μ f) / √k3 := by positivity
  have hB : MeasurableSet B :=
    (measurableSet_lt H.meas_sig measurable_const).union
      (measurableSet_lt (BstLean.Part130.measurable_normSq.comp H.hf) measurable_const)
  obtain ⟨hTail, hTailG⟩ := MF_tail_supply H hV hr hrG hk hk3 hRatio hRatioG
    hRad hRadG hgap hgapG
  have hBad := MF_excluded_sigma H hk0 hk30 hTail hTailG
  let b := sF μ f / √k * tail 2 r k + √(GamF μ f) / √k3 * tail 1 rG k3
  have hb0 : 0 ≤ b := by
    unfold b tail
    exact add_nonneg (mul_nonneg ha.le (exp_pos _).le)
      (mul_nonneg hb.le (exp_pos _).le)
  have hCoefficient : K0 / ((sF μ f / √k) * (√(GamF μ f) / √k3)) =
      K0 * √(k * k3) / (sF μ f * √(GamF μ f)) := by
    rw [sqrt_mul hk0.le]
    field_simp
    <;> ring
  have hRegular : ∀ p, p.1 ∉ B → p.2 ∉ B →
      R p ≤ (K0 / ((sF μ f / √k) * (√(GamF μ f) / √k3))) * ccF μ f p ^ 2 := by
    intro p hp1 hp2
    have h1 : sF2 μ f / k ≤ sig2F μ f p.1 := by
      exact not_lt.mp (fun h => hp1 (Or.inl h))
    have h2 : sF2 μ f / k ≤ sig2F μ f p.2 := by
      exact not_lt.mp (fun h => hp2 (Or.inl h))
    have h3 : GamF μ f / k3 ≤ normSq (f p.1) := by
      exact not_lt.mp (fun h => hp1 (Or.inr h))
    have h4 : GamF μ f / k3 ≤ normSq (f p.2) := by
      exact not_lt.mp (fun h => hp2 (Or.inr h))
    have hs1 : sF μ f / √k ≤ sgF μ f p.1 := by
      have h := sqrt_le_sqrt h1; rwa [sqrt_div H.hs.le] at h
    have hs2 : sF μ f / √k ≤ sgF μ f p.2 := by
      have h := sqrt_le_sqrt h2; rwa [sqrt_div H.hs.le] at h
    have hf1 : √(GamF μ f) / √k3 ≤ nrm (f p.1) := by
      have h := sqrt_le_sqrt h3; rwa [sqrt_div hG.le] at h
    have hf2 : √(GamF μ f) / √k3 ≤ nrm (f p.2) := by
      have h := sqrt_le_sqrt h4; rwa [sqrt_div hG.le] at h
    exact (hKernel p h1 h2 h3 h4).trans
      (regular_remainder K0_pos.le ha hb hs1 hs2 hf1 hf2)
  obtain ⟨hi, hI⟩ := MF_remainder_of_regular_bound H hB hRm hR0
    (div_nonneg K0_pos.le (mul_nonneg ha.le hb.le)) hb0 hBad hRegular hGlobal
  refine ⟨hi, hI.trans (le_of_eq ?_)⟩
  rw [hCoefficient]
  unfold b
  ring

#print axioms MF_integrated_remainder_of_kernel_bounds
end BstLean.Part194
