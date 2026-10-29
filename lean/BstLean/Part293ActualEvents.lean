import BstLean.Part293ActualPass
import BstLean.Part293PaidAssembly
import BstLean.Part293RetainedFields

/-! Actual source, latitude and table events leave the paid weighted frame explicit. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part161 BstLean.Part169
open BstLean.Part289 BstLean.BlueprintLow

noncomputable def passes_of_actualEvents {n : ℕ} (hn : LowBand n)
    (S : NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge)
    (t : ℝ) (c : Ret n)
    (hc : c ∈ (actualLedger hn S).retained.event) :
    PassSupplies t c := by
  have H := actualRetainedFields hn S hc
  have A := agentInputs_of_events hn c H.theta H.worldcentre_pos H.tau_pos
    H.source_agent H.latitude H.outputcentre H.positiveoutput
  exact (cappedPass_of_agent_table hn t c H.world_good A H.latitude
    H.outputcentre H.table).toPassSupplies hn.1

/-- This is the remaining actual frame obligation, not an unconditional supply. -/
structure RemainingFrameSupply where
  schur : ∀ n ∈ Icc (8000 : ℕ) 11882,
    NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge
  frame : ∀ n (hn : n ∈ Icc (8000 : ℕ) 11882),
    BstLean.Part157.FRAME_A_hyp (statedDesign2 n) (agentFrame / n)
      (actualLedger hn (schur n hn)).retained.event

noncomputable def RemainingFrameSupply.toPaidBandSupplies (F : RemainingFrameSupply) :
    PaidBandSupplies where
  schur := F.schur
  passes := fun n hn t c hc => passes_of_actualEvents hn (F.schur n hn) t c hc
  frame := F.frame

noncomputable def RemainingFrameSupply.toBandInputs (F : RemainingFrameSupply) :
    BandInputs := F.toPaidBandSupplies.toBandInputs

end BstLean.Part293

/-- info: 'BstLean.Part293.passes_of_actualEvents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.passes_of_actualEvents

/-- info: 'BstLean.Part293.RemainingFrameSupply.toBandInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.RemainingFrameSupply.toBandInputs
