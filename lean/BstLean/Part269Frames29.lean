import BstLean.Part269Frames29Step0
import BstLean.Part269Frames29Step1
import BstLean.Part269Frames29Step2
import BstLean.Part269Frames29Step3
import BstLean.Part269Frames29Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard29 (n : ℕ) (hn : n ∈ Icc 13075 13099) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13075.frameData13075
  · exact N13076.frameData13076
  · exact N13077.frameData13077
  · exact N13078.frameData13078
  · exact N13079.frameData13079
  · exact N13080.frameData13080
  · exact N13081.frameData13081
  · exact N13082.frameData13082
  · exact N13083.frameData13083
  · exact N13084.frameData13084
  · exact N13085.frameData13085
  · exact N13086.frameData13086
  · exact N13087.frameData13087
  · exact N13088.frameData13088
  · exact N13089.frameData13089
  · exact N13090.frameData13090
  · exact N13091.frameData13091
  · exact N13092.frameData13092
  · exact N13093.frameData13093
  · exact N13094.frameData13094
  · exact N13095.frameData13095
  · exact N13096.frameData13096
  · exact N13097.frameData13097
  · exact N13098.frameData13098
  · exact N13099.frameData13099
end BstLean.Part269
