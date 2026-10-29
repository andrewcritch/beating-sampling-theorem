import BstLean.Part269Frames14Step0
import BstLean.Part269Frames14Step1
import BstLean.Part269Frames14Step2
import BstLean.Part269Frames14Step3
import BstLean.Part269Frames14Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard14 (n : ℕ) (hn : n ∈ Icc 12700 12724) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12700.frameData12700
  · exact N12701.frameData12701
  · exact N12702.frameData12702
  · exact N12703.frameData12703
  · exact N12704.frameData12704
  · exact N12705.frameData12705
  · exact N12706.frameData12706
  · exact N12707.frameData12707
  · exact N12708.frameData12708
  · exact N12709.frameData12709
  · exact N12710.frameData12710
  · exact N12711.frameData12711
  · exact N12712.frameData12712
  · exact N12713.frameData12713
  · exact N12714.frameData12714
  · exact N12715.frameData12715
  · exact N12716.frameData12716
  · exact N12717.frameData12717
  · exact N12718.frameData12718
  · exact N12719.frameData12719
  · exact N12720.frameData12720
  · exact N12721.frameData12721
  · exact N12722.frameData12722
  · exact N12723.frameData12723
  · exact N12724.frameData12724
end BstLean.Part269
