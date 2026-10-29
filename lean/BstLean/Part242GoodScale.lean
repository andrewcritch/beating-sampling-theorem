import BstLean.Part242Reciprocal

/-! SY2 uses the normalized good transverse distribution at each retained index. -/
namespace BstLean.Part242
open MeasureTheory Real Set

variable {V : Type*} [MeasurableSpace V]

noncomputable def conditionalVariance (ν : Measure V) (z : V → ℝ) : ℝ :=
  ∫ v, (z v - ∫ u, z u ∂ν) ^ 2 ∂ν

noncomputable def goodMeanSq (ν : Measure V) (G : Set V) (z : V → ℝ) : ℝ :=
  (∫ v, z v ∂BstLean.Part162.nrm ν G) ^ 2

lemma variance_identity (ν : Measure V) [IsProbabilityMeasure ν] {z : V → ℝ}
    (mz : Measurable z) {M : ℝ} (hM : ∀ v, |z v| ≤ M) :
    conditionalVariance ν z = ∫ v, z v ^ 2 ∂ν - (∫ v, z v ∂ν) ^ 2 := by
  have iz := BstLean.Part162.intB (μ := ν) mz hM
  have iz2 := BstLean.Part162.intB (μ := ν) (mz.pow_const 2)
    (fun v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM v) 2)
  unfold conditionalVariance
  have e : (fun v => (z v - ∫ u, z u ∂ν) ^ 2) =
      fun v => 1 * z v ^ 2 + (-2 * ∫ u, z u ∂ν) * z v + (∫ u, z u ∂ν) ^ 2 := by
    funext v
    ring
  rw [e, BstLean.Part162.int_quad iz iz2]
  ring

/-- The removed mass affects the mean shift and the good variance separately. -/
theorem good_scale_loss (ν : Measure V) [IsProbabilityMeasure ν]
    {G : Set V} (hG : MeasurableSet G) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hm : 1 - η ≤ ν.real G) {z : V → ℝ} (mz : Measurable z)
    {M : ℝ} (hM : ∀ v, |z v| ≤ M) :
    (∫ v, z v ^ 2 ∂ν) - goodMeanSq ν G z ≤
      sqrt (η / (1 - η)) * sqrt (conditionalVariance ν (fun v => z v ^ 2)) +
        conditionalVariance ν z / (1 - η) := by
  have hmp : 0 < ν.real G := by linarith
  haveI := BstLean.Part162.nrm_prob ν hG hmp
  have hsq : ∀ v, |z v ^ 2| ≤ M ^ 2 := fun v => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM v) 2
  have hshift := BstLean.Part162.shift_le hG hmp (mz.pow_const 2) hsq hm hη1
  have hv := BstLean.Part162.var_le_sq_sub (μ := BstLean.Part162.nrm ν G)
    mz hM (∫ v, z v ∂ν)
  have hcenter : ∀ v, |z v - ∫ u, z u ∂ν| ≤ M + |∫ u, z u ∂ν| := fun v =>
    (abs_sub _ _).trans (add_le_add (hM v) le_rfl)
  have iv := BstLean.Part162.intB (μ := ν) ((mz.sub_const _).pow_const 2)
    (fun v => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hcenter v) 2)
  have hr := BstLean.Part162.integral_nrm_le hG hmp
    (fun v => sq_nonneg (z v - ∫ u, z u ∂ν)) iv
  have hprice : (ν.real G)⁻¹ * conditionalVariance ν z ≤
      conditionalVariance ν z / (1 - η) := by
    have h0 : 0 ≤ conditionalVariance ν z := integral_nonneg fun v => sq_nonneg _
    rw [mul_comm, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left h0 (by linarith) hm
  have hgId := variance_identity (BstLean.Part162.nrm ν G) mz hM
  have hV : conditionalVariance (BstLean.Part162.nrm ν G) z ≤
      conditionalVariance ν z / (1 - η) := hv.trans (hr.trans hprice)
  have hShift := (le_abs_self ((∫ v, z v ^ 2 ∂ν) -
    ∫ v, z v ^ 2 ∂BstLean.Part162.nrm ν G)).trans hshift
  unfold goodMeanSq
  change _ ≤ sqrt (η / (1 - η)) *
    sqrt (∫ v, (z v ^ 2 - ∫ u, z u ^ 2 ∂ν) ^ 2 ∂ν) + _
  linarith

end BstLean.Part242
