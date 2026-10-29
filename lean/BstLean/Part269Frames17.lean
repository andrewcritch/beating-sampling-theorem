import BstLean.Part269Frames17Step0
import BstLean.Part269Frames17Step1
import BstLean.Part269Frames17Step2
import BstLean.Part269Frames17Step3
import BstLean.Part269Frames17Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard17 (n : ℕ) (hn : n ∈ Icc 12775 12799) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12775.frameData12775
  · exact N12776.frameData12776
  · exact N12777.frameData12777
  · exact N12778.frameData12778
  · exact N12779.frameData12779
  · exact N12780.frameData12780
  · exact N12781.frameData12781
  · exact N12782.frameData12782
  · exact N12783.frameData12783
  · exact N12784.frameData12784
  · exact N12785.frameData12785
  · exact N12786.frameData12786
  · exact N12787.frameData12787
  · exact N12788.frameData12788
  · exact N12789.frameData12789
  · exact N12790.frameData12790
  · exact N12791.frameData12791
  · exact N12792.frameData12792
  · exact N12793.frameData12793
  · exact N12794.frameData12794
  · exact N12795.frameData12795
  · exact N12796.frameData12796
  · exact N12797.frameData12797
  · exact N12798.frameData12798
  · exact N12799.frameData12799
end BstLean.Part269
