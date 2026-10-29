import BstLean.Part291FrameEnclosure
namespace BstLean.BlueprintLow
open Real BstLean.Part254

theorem lowRotation2 : BstLean.Part195.rotationConstant 2 ≤ (2067284453287/1000000000000) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem lowRotation4 : BstLean.Part195.rotationConstant 4 ≤ (1405201457693/500000000000) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem lowRotation12 : BstLean.Part195.rotationConstant 12 ≤ (2367319965351/500000000000) := by
  apply BstLean.Part252.rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem lowFrameBad_cap : lowFrameBad ≤ (165171367/200000000000) := by
  have h1 : √(BstLean.Part254.gaussianTail lowWideWindow.pair +
      2 * (BstLean.Part255.delta / 0.00025)) ≤ (41001/500000000000) :=
    sqrt_le_iff.mpr ⟨by norm_num,lowBadMass_cap.trans (by norm_num)⟩
  have h2 : √(√(BstLean.Part254.gaussianTail lowWideWindow.pair +
      2 * (BstLean.Part255.delta / 0.00025))) ≤ (143179957/500000000000) :=
    sqrt_le_iff.mpr ⟨by norm_num,h1.trans (by norm_num)⟩
  have h3 : √(gaussianOutside lowWideWindow) ≤ (3903679/50000000000) :=
    sqrt_le_iff.mpr ⟨by norm_num,lowWideOutside_cap.trans (by norm_num)⟩
  unfold lowFrameBad
  linarith
end BstLean.BlueprintLow
