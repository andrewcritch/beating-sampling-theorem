import BstLean.Part160MFInt
import BstLean.Part194MF

/-! The actual MF second moment with the supplied Gaussian concentration tails. -/
namespace BstLean.Part198
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part153 (nrm)
open BstLean.Part154 BstLean.Part194

/-- The paper MF bound holds for the actual DF, with no covariance-kernel premise. -/
theorem MF_second_moment {d m : ℕ}
    {f : (Fin d → ℝ) → Fin m → ℝ} {L pg r rG k k3 : ℝ}
    (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hV : ∀ x y, nrm (f x - f y) ≤ L * nrm (x - y))
    (hr : 0 < r) (hrG : 0 < rG) (hk : 1 < k) (hk3 : 1 < k3)
    (hRatio : L ^ 2 / sF2 (stdGauss (Fin d)) f ≤ r)
    (hRatioG : L ^ 2 / GamF (stdGauss (Fin d)) f ≤ rG)
    (hRad : 0 ≤ 1 - 2 * r) (hRadG : 0 ≤ 1 - rG)
    (hgap : 0 < gap 2 r k) (hgapG : 0 < gap 1 rG k3) :
    let μ := stdGauss (Fin d)
    ∫ z, DF μ f z ^ 2 ∂stdGauss (Fin m) ≤
      K0 * √(k * k3) * hsF μ f / (sF μ f * √(GamF μ f)) +
        sF μ f / 4 * (sF μ f * tail 2 r k / √k +
          √(GamF μ f) * tail 1 rG k3 / √k3) +
        L ^ 2 * (1 / π * (2 * (L ^ 2 / sF2 μ f) +
          (6863 / 10000) * (GamBarF μ f / sF2 μ f) *
            nuR (L ^ 2 / sF2 μ f)) + pg) +
        sF2 μ f * QB (L ^ 2 / sF2 μ f) pg := by
  let μ := stdGauss (Fin d)
  change ∫ z, DF μ f z ^ 2 ∂stdGauss (Fin m) ≤ _
  obtain ⟨ht, htG⟩ := MF_tail_supply H hV hr hrG hk hk3 hRatio hRatioG
    hRad hRadG hgap hgapG
  have hk0 : 0 < k := by linarith
  have hk30 : 0 < k3 := by linarith
  have h := BstLean.Part160.lemmaMF_int H hk0 hk30 ht htG
  have hG := BstLean.Part160.GamF_pos H
  have hs := H.sF_pos.1
  have hden : √(sF2 μ f / k * (GamF μ f / k3)) =
      sF μ f * √(GamF μ f) / √(k * k3) := by
    rw [show sF2 μ f / k * (GamF μ f / k3) =
      (sF2 μ f * GamF μ f) / (k * k3) by ring,
      sqrt_div (mul_nonneg H.hs.le hG.le), sqrt_mul H.hs.le]
    rfl
  have hfirst : K0 * (hsF μ f / √(sF2 μ f / k * (GamF μ f / k3))) =
      K0 * √(k * k3) * hsF μ f / (sF μ f * √(GamF μ f)) := by
    rw [hden]
    field_simp
  have htail : K0 * (2 * sF μ f *
      (√(sF2 μ f / k) * tail 2 r k + √(GamF μ f / k3) * tail 1 rG k3)) ≤
      sF μ f / 4 * (sF μ f * tail 2 r k / √k +
        √(GamF μ f) * tail 1 rG k3 / √k3) := by
    rw [sqrt_div H.hs.le, sqrt_div hG.le]
    change K0 * (2 * sF μ f *
      (sF μ f / √k * tail 2 r k + √(GamF μ f) / √k3 * tail 1 rG k3)) ≤ _
    have ht0 : 0 ≤ sF μ f *
        (sF μ f / √k * tail 2 r k + √(GamF μ f) / √k3 * tail 1 rG k3) := by
      unfold tail
      positivity
    have := mul_le_mul_of_nonneg_right K0_lt.le ht0
    convert mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  have hnu : 0 ≤ nuR (L ^ 2 / sF2 μ f) := by
    unfold nuR
    exact add_nonneg (mul_nonneg (by norm_num) (div_nonneg (sq_nonneg _) H.hs.le))
      (sq_nonneg _)
  have hlin := mul_le_mul_of_nonneg_right linear_coefficient_bound
    (show 0 ≤ GamBarF μ f / sF2 μ f * nuR (L ^ 2 / sF2 μ f) from
      mul_nonneg (div_nonneg H.hbar.le H.hs.le) hnu)
  have hlin' := mul_le_mul_of_nonneg_left hlin
    (show 0 ≤ L ^ 2 * (1 / π) by positivity)
  rw [mul_add, hfirst] at h
  nlinarith only [h, htail, hlin']

#print axioms MF_second_moment
end BstLean.Part198
