import BstLean.Part293CoarseEndpoint0
import BstLean.Part293CoarseCover
import BstLean.Part293EndpointRelabel

namespace BstLean.Part293.Coarse
open BstLean.Part156 BstLean.Part232 BstLean.Part236

noncomputable def certificate0 : (i : ℕ) →
    Option (EndCertificate 8000 (worldBase + frameBoundary (0 + 1))
      agentFrame aL (rootAllowance + samplingDeviation) (radiusBoundary (i + 1)))
  | 0 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell0_0)
  | 1 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell1_0)
  | 2 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell2_0)
  | 3 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell3_0)
  | 4 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell4_0)
  | 5 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell5_0)
  | 6 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell6_0)
  | 7 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell7_0)
  | 8 => some (relabelEnd
      (by norm_num [worldBase, frameBoundary])
      (by norm_num [radiusBoundary]) cell8_0)
  | _ => none

theorem certificate0_payment (i : ℕ) (hi : i < 9) :
    cellPayment (certificate0 i) ≤ endpointIntercept + radiusPrice * radiusBoundary i ^ 2 +
      framePrice quadraticPrice linearPrice (frameBoundary 0) := by
  interval_cases i
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell0_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell1_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell2_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell3_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell4_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell5_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell6_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell7_0_payment
  · simp only [certificate0, cellPayment]
    rw [relabelEnd_payment]
    simpa only [radiusBoundary, frameBoundary] using cell8_0_payment

end BstLean.Part293.Coarse
