import BstLean.Part293CoarseRow0
import BstLean.Part293CoarseRow1
import BstLean.Part293CoarseRow2
import BstLean.Part293CoarseRow3

namespace BstLean.Part293.Coarse
open BstLean.Part156 BstLean.Part232 BstLean.Part236

noncomputable def certificate (i : ℕ) : (j : ℕ) →
    Option (EndCertificate 8000 (worldBase + frameBoundary (j + 1))
      agentFrame aL (rootAllowance + samplingDeviation) (radiusBoundary (i + 1)))
  | 0 => certificate0 i
  | 1 => certificate1 i
  | 2 => certificate2 i
  | 3 => certificate3 i
  | _ => none

noncomputable def inputs : EndpointInputs where
  radius := radiusCover
  frame := frameCover
  maximum := rfl
  certificate := certificate
  payment := by
    intro i hi j hj
    change i < 9 at hi
    change j < 4 at hj
    interval_cases j
    · exact certificate0_payment i hi
    · exact certificate1_payment i hi
    · exact certificate2_payment i hi
    · exact certificate3_payment i hi
  terminal := terminal_payment

end BstLean.Part293.Coarse

/-- info: 'BstLean.Part293.Coarse.inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.Coarse.inputs
