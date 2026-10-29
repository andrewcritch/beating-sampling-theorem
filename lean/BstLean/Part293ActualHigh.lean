import BstLean.Part293ActualEvents
import BstLean.Part293High
import BstLean.Part293Cost

/-! The full-range join with only the selected Schur and weighted frame left explicit. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part289

theorem classifier_stated2_8000_of_frameSupply (F : RemainingFrameSupply) :
    ∀ n ≥ 8000, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
        (10 ^ 12) z.1 z.2)} :=
  classifier_stated2_8000_of_low
    (classifier_stated2_8000_11882_of_supplies F.toBandInputs)

end BstLean.Part293

/-- info: 'BstLean.Part293.classifier_stated2_8000_of_frameSupply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000_of_frameSupply

/-- info: 'BstLean.Part293.statedDesign2_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.statedDesign2_cost
