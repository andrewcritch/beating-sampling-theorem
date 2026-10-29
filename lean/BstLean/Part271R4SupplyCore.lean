import BstLean.Part271R4Block
import BstLean.Part269Source
import BstLean.Part264Covariance
import BstLean.Part271GlobalMaster

/-! Scalar block supplies, independent of the full World row selector. -/
namespace BstLean.Part271.R4

structure Supplies (n : ℕ) where
  scalar : BstLean.Part263.ScalarRow n
  repair : BstLean.Part264.FrameRepair n scalar
  covariance : BstLean.Part263.CovarianceInputs n scalar.grid
    BstLean.Part255.parameters (BstLean.Part264.caps repair)
  numerics : ∀ i : Fin 60, 10 ≤ i.val ∧ i.val ≤ 52 →
    BstLean.Part269.CellSourceNumerics n (scalar.table i) scalar.M scalar.H scalar.xi
  direction_cap : scalar.M ≤ 91 / 1000
  energy_cap : scalar.H ≤ (2101 / 100) / n
  parallel_cap : scalar.xi ≤ 4 / 100
  centre_energy_cap : ∀ i : Fin 60, 10 ≤ i.val ∧ i.val ≤ 52 →
    (scalar.table i).energy ≤ 702 / 1000
  frame_cap : scalar.targetFrame ≤ BstLean.Part271.GlobalMaster.agent.frame

end BstLean.Part271.R4
