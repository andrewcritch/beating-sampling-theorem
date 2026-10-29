import BstLean.Part269Frames12Step0
import BstLean.Part269Frames12Step1
import BstLean.Part269Frames12Step2
import BstLean.Part269Frames12Step3
import BstLean.Part269Frames12Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard12 (n : ℕ) (hn : n ∈ Icc 12650 12674) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12650.frameData12650
  · exact N12651.frameData12651
  · exact N12652.frameData12652
  · exact N12653.frameData12653
  · exact N12654.frameData12654
  · exact N12655.frameData12655
  · exact N12656.frameData12656
  · exact N12657.frameData12657
  · exact N12658.frameData12658
  · exact N12659.frameData12659
  · exact N12660.frameData12660
  · exact N12661.frameData12661
  · exact N12662.frameData12662
  · exact N12663.frameData12663
  · exact N12664.frameData12664
  · exact N12665.frameData12665
  · exact N12666.frameData12666
  · exact N12667.frameData12667
  · exact N12668.frameData12668
  · exact N12669.frameData12669
  · exact N12670.frameData12670
  · exact N12671.frameData12671
  · exact N12672.frameData12672
  · exact N12673.frameData12673
  · exact N12674.frameData12674
end BstLean.Part269
