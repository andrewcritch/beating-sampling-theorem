import BstLean.Part293ActualLedger
import BstLean.Part293CoarseEndpoints
import BstLean.Part293Passes

/-! Band assembly with the actual paid World, source, latitude and table events.
Only the selected Schur charge, Agent pass and weighted frame remain as inputs. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part289
open BstLean.BlueprintLow

structure PaidBandSupplies where
  schur : ∀ n ∈ Icc (8000 : ℕ) 11882,
    NetworkCharge (retDist (statedDesign2 n).toCentres) schurCharge
  passes : ∀ n (hn : n ∈ Icc (8000 : ℕ) 11882) (t : ℝ) (c : Ret n),
    c ∈ (actualLedger hn (schur n hn)).retained.event → PassSupplies t c
  frame : ∀ n (hn : n ∈ Icc (8000 : ℕ) 11882),
    FRAME_A_hyp (statedDesign2 n) (agentFrame / n)
      (actualLedger hn (schur n hn)).retained.event

noncomputable def PaidBandSupplies.toBandInputs (A : PaidBandSupplies) : BandInputs where
  endpoint := Coarse.inputs
  rows := fun n hn t => {
    event := (actualLedger hn (A.schur n hn)).retained
    world := worldInputs_of_supply hn.1 (worldSupplyBand hn.1 hn.2)
      (actualLedger_hidden hn (A.schur n hn))
    agent := A.frame n hn
    root := rootPrice_of_pass hn.1 t
      (fun c hc => (A.passes n hn t c hc).toRootInputs hn.1 hn.2) }

theorem classifier_stated2_8000_11882_of_paid (A : PaidBandSupplies) :
    ∀ n ∈ Icc (8000 : ℕ) 11882, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
        (10 ^ 12) z.1 z.2)} :=
  classifier_stated2_8000_11882_of_supplies A.toBandInputs

end BstLean.Part293

/-- info: 'BstLean.Part293.classifier_stated2_8000_11882_of_paid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000_11882_of_paid
