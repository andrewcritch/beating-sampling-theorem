import BstLean.Part269Frames21Step0
import BstLean.Part269Frames21Step1
import BstLean.Part269Frames21Step2
import BstLean.Part269Frames21Step3
import BstLean.Part269Frames21Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard21 (n : ℕ) (hn : n ∈ Icc 12875 12899) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12875.frameData12875
  · exact N12876.frameData12876
  · exact N12877.frameData12877
  · exact N12878.frameData12878
  · exact N12879.frameData12879
  · exact N12880.frameData12880
  · exact N12881.frameData12881
  · exact N12882.frameData12882
  · exact N12883.frameData12883
  · exact N12884.frameData12884
  · exact N12885.frameData12885
  · exact N12886.frameData12886
  · exact N12887.frameData12887
  · exact N12888.frameData12888
  · exact N12889.frameData12889
  · exact N12890.frameData12890
  · exact N12891.frameData12891
  · exact N12892.frameData12892
  · exact N12893.frameData12893
  · exact N12894.frameData12894
  · exact N12895.frameData12895
  · exact N12896.frameData12896
  · exact N12897.frameData12897
  · exact N12898.frameData12898
  · exact N12899.frameData12899
end BstLean.Part269
