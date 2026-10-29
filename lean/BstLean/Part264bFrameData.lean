import BstLean.Part259Reuse
import BstLean.Part264Frame12226

/-! The local-frame fields that the final RowInputs assembly consumes. -/
namespace BstLean.Part264b
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part156 BstLean.Part192 BstLean.Part196
open BstLean.Part160 (AgFam agentEv)
open BstLean.Part169 (paperDesignP)

structure FrameData (n : ℕ) where
  worldParameters : WorldParameters
  world : WorldPackage (paperProgram n) worldParameters
  covarianceEvent : Set (AgFam n)
  cell : Fin 60 → Set ℝ
  caps : Fin 60 → ℝ
  covariance_measurable : MeasurableSet covarianceEvent
  covariance_payment : (retDist (paperCentres n)).real
    (agentEv (paperDesignP n) covarianceEvent)ᶜ ≤ (1/4000 : ℝ)
  baseEvent : Set (Ret n)
  base_measurable : MeasurableSet baseEvent
  frameAllowance : ℝ
  frame : ∀ {hW : ℝ} c,
    c ∈ goodSet (BstLean.Part159.Hof world.hidden)
      (baseEvent ∩ BstLean.Part259.covarianceGood covarianceEvent)
      (HbarW (paperDesignP n)) hW →
    Nonempty (BstLean.Part259.LocalFrameInputs n covarianceEvent cell caps c frameAllowance)

noncomputable def frameData12225 : FrameData 12225 where
  worldParameters := BstLean.Part259.row12225.worldParameters
  world := BstLean.Part259.row12225.world
  covarianceEvent := BstLean.Part259.row12225.covarianceEvent
  cell := BstLean.Part259.row12225.cell
  caps := BstLean.Part259.row12225.caps
  covariance_measurable := BstLean.Part259.row12225.covariance_measurable
  covariance_payment := BstLean.Part259.row12225.covariance_payment
  baseEvent := BstLean.Part259.row12225.baseEvent
  base_measurable := BstLean.Part259.row12225.base_measurable
  frameAllowance := BstLean.Part259.row12225.agentParameters.frame
  frame := by
    intro hW c hc
    have ha := hc.2.1.1.1.1
    have hang := BstLean.Part252.analyticBaseCertificate.angles ha
    have hwin := BstLean.Part250.internalWorld.noise_window c ⟨hc.1.1,hang⟩
    obtain ⟨i,hi,hm⟩ := BstLean.Part258.cells_cover hwin
    exact ⟨BstLean.Part259.frameInputs_of_12225 (BstLean.Part258.selectedFrameInputs hi hm
      (BstLean.Part257.sourceEvents_of_base hc.1.1 hc.2.1))⟩

noncomputable def frameData12226 : FrameData 12226 where
  worldParameters := BstLean.Part260.worldParameters 12226
  world := BstLean.Part260.worldPackage 12226 (by constructor <;> norm_num)
  covarianceEvent := BstLean.Part264.covarianceEvent12226
  cell := BstLean.Part263.cell BstLean.Part263.scalarRow12226.grid
  caps := BstLean.Part264.caps BstLean.Part264.repair12226
  covariance_measurable := BstLean.Part264.covarianceEvent12226_measurable
  covariance_payment := BstLean.Part264.covarianceEvent12226_payment
  baseEvent := BstLean.Part262.sourceBase 12226
  base_measurable := BstLean.Part262.sourceBase_measurable (by norm_num)
  frameAllowance := BstLean.Part259.agent12226.frame
  frame := BstLean.Part264.frame12226

end BstLean.Part264b
