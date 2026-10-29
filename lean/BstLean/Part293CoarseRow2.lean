import BstLean.Part293CoarseEndpoint2
import BstLean.Part293CoarseCover
import BstLean.Part293EndpointRelabel

namespace BstLean.Part293.Coarse
open BstLean.Part156 BstLean.Part232 BstLean.Part236

noncomputable def certificate2 : (i : ℕ) →
    Option (EndCertificate 8000 (worldBase + frameBoundary (2 + 1))
      agentFrame aL (rootAllowance + samplingDeviation) (radiusBoundary (i + 1)))
  | 0 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell0_2)
  | 1 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell1_2)
  | 2 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell2_2)
  | 3 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell3_2)
  | 4 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell4_2)
  | 5 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell5_2)
  | 6 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell6_2)
  | 7 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell7_2)
  | 8 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell8_2)
  | _ => none

theorem certificate2_payment (i : ℕ) (hi : i < 9) :
    cellPayment (certificate2 i) ≤ endpointIntercept + radiusPrice * radiusBoundary i ^ 2 +
      framePrice quadraticPrice linearPrice (frameBoundary 2) := by
  interval_cases i
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell0_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell1_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell2_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell3_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell4_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell5_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell6_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell7_2_payment
  · simp only [certificate2, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell8_2_payment

end BstLean.Part293.Coarse
