import BstLean.Part293ActualHigh
import BstLean.Part293FrameAdapter
import BstLean.Part291WeightedFrame

/-! Final band and full-range assembly. Acceptance requires all actual supply imports. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part161 BstLean.Part169
open BstLean.Part188 BstLean.Part289 BstLean.BlueprintLow

noncomputable def actualFrameSupply : RemainingFrameSupply :=
  frameSupply_of_band_tests (by
    intro n hn c hw hc hτ hC hS v hv
    exact weightedFrameBand hn c hw hc hτ hC hS v hv)

theorem classifier_stated2_8000_11882 :
    ∀ n ∈ Icc (8000 : ℕ) 11882, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
        (10 ^ 12) z.1 z.2)} :=
  classifier_stated2_8000_11882_of_supplies actualFrameSupply.toBandInputs

theorem classifier_stated2_8000 :
    ∀ n ≥ 8000, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {z | successNet z.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
        (10 ^ 12) z.1 z.2)} :=
  classifier_stated2_8000_of_low classifier_stated2_8000_11882

end BstLean.Part293

/-! Guards for the two unconditional classifiers and their counted program. -/

/-- info: 'BstLean.Part293.classifier_stated2_8000_11882' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000_11882

/-- info: 'BstLean.Part293.classifier_stated2_8000' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000

/-- info: 'BstLean.Part293.statedDesign2_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.statedDesign2_cost
