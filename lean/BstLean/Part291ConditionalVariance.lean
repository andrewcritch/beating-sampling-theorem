import BstLean.Part291ConditionalSplit
import BstLean.Part242WeightedVariance
import BstLean.Part242MixturePass
import BstLean.Part248Network

/-! Actual conditional second moments. The normalized inner measure and the
unnormalized outer restriction are retained explicitly. -/
namespace BstLean.BlueprintLow
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part242 BstLean.Part248

theorem paper_conditional_variances {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {wl ws σl η : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1)
    {a : Ix n} (ha : a ∈ keptIx D c (dPaper D c wl ws σl η h0 h1)) :
    let split := dPaper D c wl ws σl η h0 h1
    let ν := stdGauss (Fin (n - 1))
    let Z := goodMeanSq ν (slice split a) (sgA D c a)
    condMom split (epsF D c split) 2 a ≤
      (4 * (1 + ws / σl) ^ 2 / (1 - η)) * (conditionalVariance ν (sgA D c a) / Z) ∧
    condMom split (delF D c split) 2 a ≤
      (normSq c.2.1.2 / (1 - η)) * (conditionalVariance ν (lA D c a) / Z) := by
  dsimp only
  let split := dPaper D c wl ws σl η h0 h1
  let ν := stdGauss (Fin (n - 1))
  obtain ⟨hm, hm1, hS, hl, hGψ, hGφ⟩ := kept_facts hn D c h0 h1 ha
  have mS := measurable_sgA_left D c a
  have mL := measurable_lA_left D c a
  have bS := fun v => abs_sgA_le hn D c a v
  have bL := fun v => abs_lA_le hn D c a v
  have ms := measurableSet_slice split a
  haveI : IsProbabilityMeasure (nrm ν (slice split a)) := nrm_prob ν ms hm
  have hgm : 0 < goodMeanSq ν (slice split a) (sgA D c a) := by
    have h := good_mean_sq_lower ν ms hm mS bS hσl.le (fun v hv => (hGψ v hv).2)
    exact lt_of_lt_of_le (sq_pos_of_pos hσl) h
  have hSgm : goodMeanSq ν (slice split a) (sgA D c a) ≤
      ∫ v, sgA D c a v ^ 2 ∂nrm ν (slice split a) := mean_sq_le mS bS
  constructor
  · rw [cm_eps hn D c h0 h1 ha (by norm_num : (2 : ℕ) ≠ 0)]
    simp only [sq_abs]
    exact weighted_eps_variance ms hm mS bS hws hσl hm1 h1 hGψ
  · rw [cm_del hn D c h0 h1 ha (by norm_num : (2 : ℕ) ≠ 0)]
    simp only [sq_abs]
    exact weighted_location_variance ms hm mL bL hgm hSgm (normSq_nonneg _) hm1 h1

/-- Transfer an outer norm bound on the actual variance quotient. -/
theorem paper_conditional_variance_norms {n : ℕ} (hn : 1 ≤ n) (D : Design n) (c : Ret n)
    {wl ws σl η A B : ℝ} (hws : 0 ≤ ws) (hσl : 0 < σl) (h0 : 0 < η) (h1 : η < 1)
    {j : ℝ≥0∞}
    (hA : let split := dPaper D c wl ws σl η h0 h1
      LBound ((muI n).restrict (keptIx D c split)) j
        (fun a => (4 * (1 + ws / σl) ^ 2 / (1 - η)) *
          (conditionalVariance (stdGauss (Fin (n - 1))) (sgA D c a) /
            goodMeanSq (stdGauss (Fin (n - 1))) (slice split a) (sgA D c a))) A)
    (hB : let split := dPaper D c wl ws σl η h0 h1
      LBound ((muI n).restrict (keptIx D c split)) j
        (fun a => (normSq c.2.1.2 / (1 - η)) *
          (conditionalVariance (stdGauss (Fin (n - 1))) (lA D c a) /
            goodMeanSq (stdGauss (Fin (n - 1))) (slice split a) (sgA D c a))) B) :
    let split := dPaper D c wl ws σl η h0 h1
    LBound ((muI n).restrict (keptIx D c split)) j (condMom split (epsF D c split) 2) A ∧
    LBound ((muI n).restrict (keptIx D c split)) j (condMom split (delF D c split) 2) B := by
  let split := dPaper D c wl ws σl η h0 h1
  have mK : MeasurableSet (keptIx D c split) :=
    measurableSet_keptSet _ split.mgood (measurableSet_bulkIx D c) _
  constructor
  · apply hA.mono (measurable_condMom split (measurable_epsF D c split) 2)
    apply (ae_restrict_iff' mK).mpr
    exact ae_of_all _ fun a ha => by
      rw [abs_of_nonneg (condMom_nonneg split _ 2 a)]
      exact (paper_conditional_variances hn D c hws hσl h0 h1 ha).1.trans (le_abs_self _)
  · apply hB.mono (measurable_condMom split (measurable_delF D c split) 2)
    apply (ae_restrict_iff' mK).mpr
    exact ae_of_all _ fun a ha => by
      rw [abs_of_nonneg (condMom_nonneg split _ 2 a)]
      exact (paper_conditional_variances hn D c hws hσl h0 h1 ha).2.trans (le_abs_self _)

end BstLean.BlueprintLow
