import BstLean.Part293CoarseEndpoint1
import BstLean.Part293CoarseCover
import BstLean.Part293EndpointRelabel

namespace BstLean.Part293.Coarse
open BstLean.Part156 BstLean.Part232 BstLean.Part236

noncomputable def certificate1 : (i : ℕ) →
    Option (EndCertificate 8000 (worldBase + frameBoundary (1 + 1))
      agentFrame aL (rootAllowance + samplingDeviation) (radiusBoundary (i + 1)))
  | 0 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell0_1)
  | 1 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell1_1)
  | 2 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell2_1)
  | 3 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell3_1)
  | 4 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell4_1)
  | 5 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell5_1)
  | 6 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell6_1)
  | 7 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell7_1)
  | 8 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell8_1)
  | _ => none

theorem certificate1_payment (i : ℕ) (hi : i < 9) :
    cellPayment (certificate1 i) ≤ endpointIntercept + radiusPrice * radiusBoundary i ^ 2 +
      framePrice quadraticPrice linearPrice (frameBoundary 1) := by
  interval_cases i
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell0_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell1_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell2_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell3_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell4_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell5_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell6_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell7_1_payment
  · simp only [certificate1, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell8_1_payment

end BstLean.Part293.Coarse
