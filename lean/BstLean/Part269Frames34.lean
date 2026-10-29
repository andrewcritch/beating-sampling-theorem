import BstLean.Part269Frames34Step0
import BstLean.Part269Frames34Step1
import BstLean.Part269Frames34Step2
import BstLean.Part269Frames34Step3
import BstLean.Part269Frames34Step4
import BstLean.Part269Frame13224
namespace BstLean.Part269
open Set
noncomputable def frameShard34 (n : ℕ) (hn : n ∈ Icc 13200 13224) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13200.frameData13200
  · exact N13201.frameData13201
  · exact N13202.frameData13202
  · exact N13203.frameData13203
  · exact N13204.frameData13204
  · exact N13205.frameData13205
  · exact N13206.frameData13206
  · exact N13207.frameData13207
  · exact N13208.frameData13208
  · exact N13209.frameData13209
  · exact N13210.frameData13210
  · exact N13211.frameData13211
  · exact N13212.frameData13212
  · exact N13213.frameData13213
  · exact N13214.frameData13214
  · exact N13215.frameData13215
  · exact N13216.frameData13216
  · exact N13217.frameData13217
  · exact N13218.frameData13218
  · exact N13219.frameData13219
  · exact N13220.frameData13220
  · exact N13221.frameData13221
  · exact N13222.frameData13222
  · exact N13223.frameData13223
  · exact N13224.frameData13224
end BstLean.Part269
