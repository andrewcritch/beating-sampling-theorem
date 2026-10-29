import BstLean.Part269Frames30Step0
import BstLean.Part269Frames30Step1
import BstLean.Part269Frames30Step2
import BstLean.Part269Frames30Step3
import BstLean.Part269Frames30Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard30 (n : ℕ) (hn : n ∈ Icc 13100 13124) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13100.frameData13100
  · exact N13101.frameData13101
  · exact N13102.frameData13102
  · exact N13103.frameData13103
  · exact N13104.frameData13104
  · exact N13105.frameData13105
  · exact N13106.frameData13106
  · exact N13107.frameData13107
  · exact N13108.frameData13108
  · exact N13109.frameData13109
  · exact N13110.frameData13110
  · exact N13111.frameData13111
  · exact N13112.frameData13112
  · exact N13113.frameData13113
  · exact N13114.frameData13114
  · exact N13115.frameData13115
  · exact N13116.frameData13116
  · exact N13117.frameData13117
  · exact N13118.frameData13118
  · exact N13119.frameData13119
  · exact N13120.frameData13120
  · exact N13121.frameData13121
  · exact N13122.frameData13122
  · exact N13123.frameData13123
  · exact N13124.frameData13124
end BstLean.Part269
