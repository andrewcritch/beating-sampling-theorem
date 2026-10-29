import BstLean.Part243Payments
import BstLean.Part243Bridge

/-! Part 243: the 12225 scalar certificate and its conditional network transfer.
No declaration supplies the missing numerical World or retained Agent events. -/
namespace BstLean.Part243
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)

noncomputable def rowWorldParameters (hidden : ℝ) : WorldParameters where
  hiddenCharge := hidden
  frame := rowWorldFrame
  moment := rowMoment
  productLo := 2
  productHi := 21 / 10
  noiseLo := 46 / 100
  noiseHi := 528 / 1000

/-- Unused Agent fields do not assert analytic supplies. -/
noncomputable def rowAgentParameters (retained : ℝ) : AgentParameters :=
  { agentLedgerParameters with charge := retained, frame := rowAgentFrame, root := rowRoot }

/-- All scalar fields of the original master are checked at the prescribed endpoint.
Only the combined event charge remains a numerical premise. -/
noncomputable def rowCertificate {hidden retained : ℝ}
    (hr : 0 ≤ retained) (hcharge : hidden + retained ≤ rowEventAllowance) :
    MasterCertificate 12225 (rowWorldParameters hidden) (rowAgentParameters retained) where
  dimensionLo := 12225
  dimensionHi := 12225
  dimension_mem := ⟨le_rfl, le_rfl⟩
  noiseLo := 46 / 100
  noiseHi := 528 / 1000
  overlapLo := 0
  overlapHi := 1
  radiusLo := 0
  radiusHi := rowRadius
  frameLo := rowWorldFrame
  frameHi := rowAgentFrame
  noise_order := by norm_num
  overlap_order := by norm_num
  radius_order := by norm_num [rowRadius]
  frame_order := by norm_num [rowWorldFrame, rowAgentFrame]
  worldFrame_pos := by norm_num [rowWorldParameters, rowWorldFrame]
  agentFrame_pos := by norm_num [rowAgentParameters, rowAgentFrame]
  worldRadius := rowRadius
  worldRadius_pos := by norm_num [rowRadius]
  agentRoot_nonneg := by norm_num [rowAgentParameters, rowRoot]
  retainedCharge := retained
  samplingCharge := rowSamplingAllowance
  upperTail := rowPositiveBase ^ 8
  lowerTail := rowNegativeBase ^ 8
  retainedCharge_nonneg := hr
  samplingCharge_nonneg := by norm_num [rowSamplingAllowance]
  upperTail_nonneg := by positivity
  lowerTail_nonneg := by positivity
  totalBudget := rowFailureAllowance
  ledger := row_complete_scalar_ledger hcharge
  budget := row_complete_budget.le
  sampleRoot := dsL
  positiveTilt := rowPositiveTilt
  negativeTilt := rowNegativeTilt
  positiveExponent := rowPositiveExponent
  negativeExponent := rowNegativeExponent
  sampleRoot_pos := by norm_num [dsL]
  positiveTilt_pos := by norm_num [rowPositiveTilt]
  negativeTilt_neg := by norm_num [rowNegativeTilt]
  positiveExponent_nonneg := by norm_num [rowPositiveExponent]
  negativeExponent_nonneg := by norm_num [rowNegativeExponent]
  positive_enclosure := row_positive_enclosure
  negative_enclosure := row_negative_enclosure
  positive_tail := row_positive_tail
  negative_tail := row_negative_tail
  sampling_payment := row_sampling
  lower_radius := row_radius_guards.1
  lower_root := row_radius_guards.2
  actual_sampling := by
    have he : -((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2 = -100 := by norm_num [dsL]
    rw [he]
    exact row_sampling

noncomputable def proposedHiddenCharge : ℝ := 1194124330168 / 10 ^ 15
noncomputable def proposedRetainedCharge : ℝ :=
  495214276589 / 10 ^ 15 + 1 / 4000 + 106144212354 / 10 ^ 15 +
    1052754646384 / 10 ^ 15 + 6144212354 / 10 ^ 15

/-- This is a complete scalar certificate with no numerical premise.
Its event allowances remain proposed bounds until actual packages supply them. -/
noncomputable def certifiedScalarRow :
    MasterCertificate 12225 (rowWorldParameters proposedHiddenCharge)
      (rowAgentParameters proposedRetainedCharge) :=
  rowCertificate (by norm_num [proposedRetainedCharge])
    (row_event_allocation le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl)

/-- Scalar acceptance transfers to the actual networks only with both event packages. -/
theorem row_classifier_conditional {hidden retained : ℝ}
    (hr : 0 ≤ retained) (hcharge : hidden + retained ≤ rowEventAllowance)
    (W : WorldPackage (paperProgram 12225) (rowWorldParameters hidden)) (t : ℝ)
    (A : AgentPackage 12225 (BstLean.Part159.Hof W.hidden)
      rowRadius rowAgentFrame rowRoot retained t) :
    99 / 100 ≤ ((mlpTriple 2 12225).prod (sampMeas (10 ^ 12) 12225)).real
      {x | successNet x.1 t (progOut (paperDesignP 12225) t aL (10 ^ 12) x.1 x.2)} :=
  checked_junction (by norm_num) W t (rowCertificate hr hcharge) A le_rfl

end BstLean.Part243
#print axioms BstLean.Part243.rowCertificate
#print axioms BstLean.Part243.certifiedScalarRow
#print axioms BstLean.Part243.row_classifier_conditional
