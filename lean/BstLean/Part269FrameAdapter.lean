import BstLean.Part269WorldSource
import BstLean.Part264Covariance

namespace BstLean.Part269
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part192
open BstLean.Part263 (ScalarRow CovarianceInputs covarianceEvent cell)
open BstLean.Part264 (FrameRepair caps)

noncomputable def frameData_from_numerics {n : ℕ} (hn : 12225 ≤ n) (hu : n ≤ 16384)
    {wp : WorldParameters} (W : WorldPackage (paperProgram n) wp)
    (hidden_eq : W.hidden = BstLean.Part227.hidden n (44945/10^6) (4/10000) (712/10000)
      (178/10^8) (1232/10^7))
    (lower : (202225/100000 : ℝ) ≤ BstLean.Part227.productLower n (1232/10^7))
    (upper : BstLean.Part227.productUpper n (1232/10^7) ≤ (202831/100000 : ℝ))
    (R : ScalarRow n) (A : FrameRepair n R)
    (C : CovarianceInputs n R.grid BstLean.Part255.parameters (caps A))
    (N : ∀ i : Fin 60, (10 ≤ i.val ∧ i.val ≤ 52) →
      CellSourceNumerics n (R.table i) R.M R.H R.xi)
    (allowance : ℝ) (hallowance : R.targetFrame = allowance) : BstLean.Part264b.FrameData n where
  worldParameters := wp
  world := W
  covarianceEvent := covarianceEvent n R.grid BstLean.Part255.parameters
  cell := cell R.grid
  caps := caps A
  covariance_measurable := BstLean.Part263.covarianceEvent_measurable _ _ _
  covariance_payment := BstLean.Part263.covarianceEvent_payment (by omega) C
  baseEvent := BstLean.Part262.sourceBase n
  base_measurable := BstLean.Part262.sourceBase_measurable (by omega)
  frameAllowance := allowance
  frame := by
    intro hW c hc
    have hθ := exact_world_window (by omega : 4096 ≤ n) W hidden_eq lower upper hc.1.1 hc.2.1
    obtain ⟨i,hi,hm⟩ := BstLean.Part263.scalarRow_world_cover R hθ
    have F := frameInputs_from_numeric_sources (n := n) (R := R) (c := c) (i := i)
      hn hu A C hi hm (N i hi) (direction_from_exact_window hn hθ)
      (events_from_exact_window hn W hc.1.1 hc.2.1 hθ)
    rw [hallowance] at F
    exact ⟨F⟩

end BstLean.Part269
