import BstLean.Part269Frames11Step0
import BstLean.Part269Frames11Step1
import BstLean.Part269Frames11Step2
import BstLean.Part269Frames11Step3
import BstLean.Part269Frames11Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard11 (n : ℕ) (hn : n ∈ Icc 12625 12649) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12625.frameData12625
  · exact N12626.frameData12626
  · exact N12627.frameData12627
  · exact N12628.frameData12628
  · exact N12629.frameData12629
  · exact N12630.frameData12630
  · exact N12631.frameData12631
  · exact N12632.frameData12632
  · exact N12633.frameData12633
  · exact N12634.frameData12634
  · exact N12635.frameData12635
  · exact N12636.frameData12636
  · exact N12637.frameData12637
  · exact N12638.frameData12638
  · exact N12639.frameData12639
  · exact N12640.frameData12640
  · exact N12641.frameData12641
  · exact N12642.frameData12642
  · exact N12643.frameData12643
  · exact N12644.frameData12644
  · exact N12645.frameData12645
  · exact N12646.frameData12646
  · exact N12647.frameData12647
  · exact N12648.frameData12648
  · exact N12649.frameData12649
end BstLean.Part269
