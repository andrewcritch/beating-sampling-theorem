import BstLean.Part262ActualInterface
import BstLean.Part259Family

/-! Complete row assembly with explicit World, frame and local root supplies. -/
namespace BstLean.Part270
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part188 BstLean.Part192 BstLean.Part196
open BstLean.Part169 (paperDesignP)

noncomputable def row_from_supplies {n : ℕ} {w : WorldParameters}
    (W : WorldPackage (paperProgram n) w) (a : AgentParameters)
    (C : MasterCertificate n w a)
    (K : BstLean.Part262.ActualRootCertificate n a.root)
    (event : Set (BstLean.Part160.AgFam n))
    (cell : Fin 60 → Set ℝ) (caps : Fin 60 → ℝ)
    (hmeas : MeasurableSet event)
    (hpay : (retDist (paperCentres n)).real
      (BstLean.Part160.agentEv (paperDesignP n) event)ᶜ ≤ (1/4000 : ℝ))
    (frame : ∀ {hW : ℝ} c, c ∈ goodSet (BstLean.Part159.Hof W.hidden)
      (BstLean.Part262.sourceBase n ∩ BstLean.Part259.covarianceGood event)
      (HbarW (paperDesignP n)) hW →
      Nonempty (BstLean.Part259.LocalFrameInputs n event cell caps c a.frame))
    (L : BstLean.Part262.LocalRootSupply n (BstLean.Part159.Hof W.hidden))
    (payment : (1499145/10^9 : ℝ)+3/10000 ≤ a.charge)
    (compatible : a.charge ≤ C.retainedCharge) : BstLean.Part259.RowInputs n where
  dimension := by have := K.dimension; omega
  worldParameters := w
  agentParameters := a
  world := W
  certificate := C
  covarianceEvent := event
  cell := cell
  caps := caps
  covariance_measurable := hmeas
  covariance_payment := hpay
  baseEvent := BstLean.Part262.sourceBase n
  base_measurable := BstLean.Part262.sourceBase_measurable
    (by have := K.dimension; omega)
  baseCharge := 1499145/10^9
  base_payment := (BstLean.Part262.sourceBase_charge K.dimension K.table_payment _).trans
    (by norm_num)
  frame := fun c hc => frame c hc
  root := by
    intro t c hc
    exact ⟨K.inputs t c (L.window c hc.1.1 hc.2.1) hc.2.1
      (L.interfaces c hc.1.1 hc.2.1) (L.energy_cap c hc.1.1 hc.2.1)⟩
  payment := payment
  charge_compatible := compatible

end BstLean.Part270
