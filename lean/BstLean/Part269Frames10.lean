import BstLean.Part269Frames10Step0
import BstLean.Part269Frames10Step1
import BstLean.Part269Frames10Step2
import BstLean.Part269Frames10Step3
import BstLean.Part269Frames10Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard10 (n : ℕ) (hn : n ∈ Icc 12600 12624) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12600.frameData12600
  · exact N12601.frameData12601
  · exact N12602.frameData12602
  · exact N12603.frameData12603
  · exact N12604.frameData12604
  · exact N12605.frameData12605
  · exact N12606.frameData12606
  · exact N12607.frameData12607
  · exact N12608.frameData12608
  · exact N12609.frameData12609
  · exact N12610.frameData12610
  · exact N12611.frameData12611
  · exact N12612.frameData12612
  · exact N12613.frameData12613
  · exact N12614.frameData12614
  · exact N12615.frameData12615
  · exact N12616.frameData12616
  · exact N12617.frameData12617
  · exact N12618.frameData12618
  · exact N12619.frameData12619
  · exact N12620.frameData12620
  · exact N12621.frameData12621
  · exact N12622.frameData12622
  · exact N12623.frameData12623
  · exact N12624.frameData12624
end BstLean.Part269
