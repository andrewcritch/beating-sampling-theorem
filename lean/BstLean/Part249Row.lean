import BstLean.Part249Ledger

/-! The perturbed 12225 scalar certificate has no numerical premise.
Actual World and Agent event supplies are separate obligations. -/
namespace BstLean.Part249
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)
open BstLean.Part243

/-- Unused Agent fields do not assert analytic supplies. -/
noncomputable def optionBAgentParameters (retained : ℝ) : AgentParameters :=
  { agentLedgerParameters with charge := retained, frame := optionBAgentFrame, root := rowRoot }

/-- All scalar fields of the original master are checked at the prescribed endpoint.
Only the combined event charge remains a numerical premise. -/
noncomputable def optionBCertificate {hidden retained : ℝ}
    (hr : 0 ≤ retained) (hcharge : hidden + retained ≤ rowEventAllowance) :
    MasterCertificate 12225 (rowWorldParameters hidden) (optionBAgentParameters retained) where
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
  frameHi := optionBAgentFrame
  noise_order := by norm_num
  overlap_order := by norm_num
  radius_order := by norm_num [rowRadius]
  frame_order := by norm_num [rowWorldFrame, optionBAgentFrame]
  worldFrame_pos := by norm_num [rowWorldParameters, rowWorldFrame]
  agentFrame_pos := by norm_num [optionBAgentParameters, optionBAgentFrame]
  worldRadius := rowRadius
  worldRadius_pos := by norm_num [rowRadius]
  agentRoot_nonneg := by norm_num [optionBAgentParameters, rowRoot]
  retainedCharge := retained
  samplingCharge := rowSamplingAllowance
  upperTail := optionBPositiveBase ^ 8
  lowerTail := optionBNegativeBase ^ 8
  retainedCharge_nonneg := hr
  samplingCharge_nonneg := by norm_num [rowSamplingAllowance]
  upperTail_nonneg := by positivity
  lowerTail_nonneg := by positivity
  totalBudget := optionBFailureAllowance
  ledger := optionB_scalar_ledger hcharge
  budget := optionB_budget.le
  sampleRoot := dsL
  positiveTilt := rowPositiveTilt
  negativeTilt := rowNegativeTilt
  positiveExponent := optionBPositiveExponent
  negativeExponent := optionBNegativeExponent
  sampleRoot_pos := by norm_num [dsL]
  positiveTilt_pos := by norm_num [rowPositiveTilt]
  negativeTilt_neg := by norm_num [rowNegativeTilt]
  positiveExponent_nonneg := by norm_num [optionBPositiveExponent]
  negativeExponent_nonneg := by norm_num [optionBNegativeExponent]
  positive_enclosure := optionB_positive_enclosure
  negative_enclosure := optionB_negative_enclosure
  positive_tail := optionB_positive_tail
  negative_tail := optionB_negative_tail
  sampling_payment := row_sampling
  lower_radius := row_radius_guards.1
  lower_root := row_radius_guards.2
  actual_sampling := by
    have he : -((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2 = -100 := by norm_num [dsL]
    rw [he]
    exact row_sampling


noncomputable def optionBScalarRow :
    MasterCertificate 12225 (rowWorldParameters proposedHiddenCharge)
      (optionBAgentParameters proposedRetainedCharge) :=
  optionBCertificate (by norm_num [proposedRetainedCharge])
    (row_event_allocation le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl)

end BstLean.Part249
