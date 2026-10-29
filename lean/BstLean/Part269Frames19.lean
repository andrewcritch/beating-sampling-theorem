import BstLean.Part269Frames19Step0
import BstLean.Part269Frames19Step1
import BstLean.Part269Frames19Step2
import BstLean.Part269Frames19Step3
import BstLean.Part269Frames19Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard19 (n : ℕ) (hn : n ∈ Icc 12825 12849) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12825.frameData12825
  · exact N12826.frameData12826
  · exact N12827.frameData12827
  · exact N12828.frameData12828
  · exact N12829.frameData12829
  · exact N12830.frameData12830
  · exact N12831.frameData12831
  · exact N12832.frameData12832
  · exact N12833.frameData12833
  · exact N12834.frameData12834
  · exact N12835.frameData12835
  · exact N12836.frameData12836
  · exact N12837.frameData12837
  · exact N12838.frameData12838
  · exact N12839.frameData12839
  · exact N12840.frameData12840
  · exact N12841.frameData12841
  · exact N12842.frameData12842
  · exact N12843.frameData12843
  · exact N12844.frameData12844
  · exact N12845.frameData12845
  · exact N12846.frameData12846
  · exact N12847.frameData12847
  · exact N12848.frameData12848
  · exact N12849.frameData12849
end BstLean.Part269
