import BstLean.Part293CoarseEndpoint3
import BstLean.Part293CoarseCover
import BstLean.Part293EndpointRelabel

namespace BstLean.Part293.Coarse
open BstLean.Part156 BstLean.Part232 BstLean.Part236

noncomputable def certificate3 : (i : ℕ) →
    Option (EndCertificate 8000 (worldBase + frameBoundary (3 + 1))
      agentFrame aL (rootAllowance + samplingDeviation) (radiusBoundary (i + 1)))
  | 0 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell0_3)
  | 1 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell1_3)
  | 2 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell2_3)
  | 3 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell3_3)
  | 4 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell4_3)
  | 5 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell5_3)
  | 6 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell6_3)
  | 7 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell7_3)
  | 8 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell8_3)
  | _ => none

theorem certificate3_payment (i : ℕ) (hi : i < 9) :
    cellPayment (certificate3 i) ≤ endpointIntercept + radiusPrice * radiusBoundary i ^ 2 +
      framePrice quadraticPrice linearPrice (frameBoundary 3) := by
  interval_cases i
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell0_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell1_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell2_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell3_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell4_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell5_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell6_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell7_3_payment
  · simp only [certificate3, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell8_3_payment

end BstLean.Part293.Coarse
