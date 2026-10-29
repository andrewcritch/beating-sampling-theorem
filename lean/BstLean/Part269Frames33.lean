import BstLean.Part269Frames33Step0
import BstLean.Part269Frames33Step1
import BstLean.Part269Frames33Step2
import BstLean.Part269Frames33Step3
import BstLean.Part269Frames33Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard33 (n : ℕ) (hn : n ∈ Icc 13175 13199) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13175.frameData13175
  · exact N13176.frameData13176
  · exact N13177.frameData13177
  · exact N13178.frameData13178
  · exact N13179.frameData13179
  · exact N13180.frameData13180
  · exact N13181.frameData13181
  · exact N13182.frameData13182
  · exact N13183.frameData13183
  · exact N13184.frameData13184
  · exact N13185.frameData13185
  · exact N13186.frameData13186
  · exact N13187.frameData13187
  · exact N13188.frameData13188
  · exact N13189.frameData13189
  · exact N13190.frameData13190
  · exact N13191.frameData13191
  · exact N13192.frameData13192
  · exact N13193.frameData13193
  · exact N13194.frameData13194
  · exact N13195.frameData13195
  · exact N13196.frameData13196
  · exact N13197.frameData13197
  · exact N13198.frameData13198
  · exact N13199.frameData13199
end BstLean.Part269
