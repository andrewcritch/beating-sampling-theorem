import BstLean.Part194Gaps
import BstLean.Part154MFa

/-! Concentration supplies with the same mean-field definitions and input distribution. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part148 (EuLip)
open BstLean.Part153 (nrm nrm_sq nrm_nonneg)
open BstLean.Part154

/-- The projected norm has the HS tail with variable cutoff and variance ratio. -/
theorem MF_sigma_tail {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg r k : ℝ} (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hLip : EuLip (fun x => √(sig2F (stdGauss (Fin d)) f x)) L)
    (hr : 0 < r) (hk : 0 < k) (hRatio : L ^ 2 / sF2 (stdGauss (Fin d)) f ≤ r)
    (hRad : 0 ≤ 1 - 2 * r) (hgap : 0 < gap 2 r k) :
    (stdGauss (Fin d)).real {x | sig2F (stdGauss (Fin d)) f x <
      sF2 (stdGauss (Fin d)) f / k} ≤ tail 2 r k := by
  have hsq : ∀ x, √(sig2F (stdGauss (Fin d)) f x) ^ 2 =
      sig2F (stdGauss (Fin d)) f x := fun x => sq_sqrt (sig2F_nonneg _ _ _)
  have hi2 : Integrable (fun x => √(sig2F (stdGauss (Fin d)) f x) ^ 2)
      (stdGauss (Fin d)) := by simp_rw [hsq]; exact H.F2.1
  have hSecond : sF2 (stdGauss (Fin d)) f - 1 * L ^ 2 ≤
      ∫ x, √(sig2F (stdGauss (Fin d)) f x) ^ 2 ∂stdGauss (Fin d) := by
    simp_rw [hsq]
    rw [H.F2.2]
    linarith [H.F1.2.2.2.2]
  have ht := gaussian_tail_of_second_moment H.hℓ H.hs (by norm_num : (0 : ℝ) ≤ 1)
    hr hk hLip H.sig_int.1 hi2 (fun _ => sqrt_nonneg _) hSecond hRatio
    (by simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hRad)
    (by simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hgap)
  have hsub : {x | sig2F (stdGauss (Fin d)) f x < sF2 (stdGauss (Fin d)) f / k} ⊆
      {x | √(sig2F (stdGauss (Fin d)) f x) < √(sF2 (stdGauss (Fin d)) f) / √k} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    have h := sqrt_lt_sqrt (sig2F_nonneg _ _ _) hx
    rwa [sqrt_div H.hs.le] at h
  exact (measureReal_mono hsub).trans
    (by simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using ht)

/-- The full norm has the second tail with its own ratio and cutoff. -/
theorem MF_norm_tail {d m : ℕ} {f : (Fin d → ℝ) → Fin m → ℝ}
    {L pg r k : ℝ} (H : MFHyp (stdGauss (Fin d)) f L pg)
    (hLip : EuLip (fun x => nrm (f x)) L)
    (hr : 0 < r) (hk : 0 < k) (hRatio : L ^ 2 / GamF (stdGauss (Fin d)) f ≤ r)
    (hRad : 0 ≤ 1 - r) (hgap : 0 < gap 1 r k) :
    (stdGauss (Fin d)).real {x | normSq (f x) < GamF (stdGauss (Fin d)) f / k} ≤
      tail 1 r k := by
  have hG : 0 < GamF (stdGauss (Fin d)) f := by
    have hs := H.hs
    unfold sF2 at hs
    linarith [H.hbar]
  have hi2 : Integrable (fun x => nrm (f x) ^ 2) (stdGauss (Fin d)) := by
    simp_rw [nrm_sq]; exact H.int_sq
  have hi : Integrable (fun x => nrm (f x)) (stdGauss (Fin d)) := by
    refine ((integrable_const (1 : ℝ)).add H.int_sq).mono'
      (hLip.continuous H.hℓ.le).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (nrm_nonneg _)]
    simp only [Pi.add_apply]
    have he := nrm_sq (f x)
    nlinarith [sq_nonneg (nrm (f x) - 1)]
  have hSecond : GamF (stdGauss (Fin d)) f - 0 * L ^ 2 ≤
      ∫ x, nrm (f x) ^ 2 ∂stdGauss (Fin d) := by
    simp only [zero_mul, sub_zero, nrm_sq]; exact le_rfl
  have ht := gaussian_tail_of_second_moment H.hℓ hG (by norm_num : (0 : ℝ) ≤ 0)
    hr hk hLip hi hi2 (fun _ => nrm_nonneg _) hSecond hRatio
    (by simpa using hRad) (by simpa using hgap)
  have hsub : {x | normSq (f x) < GamF (stdGauss (Fin d)) f / k} ⊆
      {x | nrm (f x) < √(GamF (stdGauss (Fin d)) f) / √k} := by
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    have h := sqrt_lt_sqrt (BstLean.Part130.normSq_nonneg (f x)) hx
    rwa [sqrt_div hG.le] at h
  exact (measureReal_mono hsub).trans (by simpa using ht)

#print axioms MF_sigma_tail
#print axioms MF_norm_tail
end BstLean.Part194
