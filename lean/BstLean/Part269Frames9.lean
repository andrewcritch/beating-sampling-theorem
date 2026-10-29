import BstLean.Part269Frames9Step0
import BstLean.Part269Frames9Step1
import BstLean.Part269Frames9Step2
import BstLean.Part269Frames9Step3
import BstLean.Part269Frames9Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard9 (n : ℕ) (hn : n ∈ Icc 12575 12599) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12575.frameData12575
  · exact N12576.frameData12576
  · exact N12577.frameData12577
  · exact N12578.frameData12578
  · exact N12579.frameData12579
  · exact N12580.frameData12580
  · exact N12581.frameData12581
  · exact N12582.frameData12582
  · exact N12583.frameData12583
  · exact N12584.frameData12584
  · exact N12585.frameData12585
  · exact N12586.frameData12586
  · exact N12587.frameData12587
  · exact N12588.frameData12588
  · exact N12589.frameData12589
  · exact N12590.frameData12590
  · exact N12591.frameData12591
  · exact N12592.frameData12592
  · exact N12593.frameData12593
  · exact N12594.frameData12594
  · exact N12595.frameData12595
  · exact N12596.frameData12596
  · exact N12597.frameData12597
  · exact N12598.frameData12598
  · exact N12599.frameData12599
end BstLean.Part269
