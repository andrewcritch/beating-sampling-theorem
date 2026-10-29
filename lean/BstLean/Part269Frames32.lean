import BstLean.Part269Frames32Step0
import BstLean.Part269Frames32Step1
import BstLean.Part269Frames32Step2
import BstLean.Part269Frames32Step3
import BstLean.Part269Frames32Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard32 (n : ℕ) (hn : n ∈ Icc 13150 13174) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13150.frameData13150
  · exact N13151.frameData13151
  · exact N13152.frameData13152
  · exact N13153.frameData13153
  · exact N13154.frameData13154
  · exact N13155.frameData13155
  · exact N13156.frameData13156
  · exact N13157.frameData13157
  · exact N13158.frameData13158
  · exact N13159.frameData13159
  · exact N13160.frameData13160
  · exact N13161.frameData13161
  · exact N13162.frameData13162
  · exact N13163.frameData13163
  · exact N13164.frameData13164
  · exact N13165.frameData13165
  · exact N13166.frameData13166
  · exact N13167.frameData13167
  · exact N13168.frameData13168
  · exact N13169.frameData13169
  · exact N13170.frameData13170
  · exact N13171.frameData13171
  · exact N13172.frameData13172
  · exact N13173.frameData13173
  · exact N13174.frameData13174
end BstLean.Part269
