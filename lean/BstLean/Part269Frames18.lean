import BstLean.Part269Frames18Step0
import BstLean.Part269Frames18Step1
import BstLean.Part269Frames18Step2
import BstLean.Part269Frames18Step3
import BstLean.Part269Frames18Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard18 (n : ℕ) (hn : n ∈ Icc 12800 12824) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12800.frameData12800
  · exact N12801.frameData12801
  · exact N12802.frameData12802
  · exact N12803.frameData12803
  · exact N12804.frameData12804
  · exact N12805.frameData12805
  · exact N12806.frameData12806
  · exact N12807.frameData12807
  · exact N12808.frameData12808
  · exact N12809.frameData12809
  · exact N12810.frameData12810
  · exact N12811.frameData12811
  · exact N12812.frameData12812
  · exact N12813.frameData12813
  · exact N12814.frameData12814
  · exact N12815.frameData12815
  · exact N12816.frameData12816
  · exact N12817.frameData12817
  · exact N12818.frameData12818
  · exact N12819.frameData12819
  · exact N12820.frameData12820
  · exact N12821.frameData12821
  · exact N12822.frameData12822
  · exact N12823.frameData12823
  · exact N12824.frameData12824
end BstLean.Part269
