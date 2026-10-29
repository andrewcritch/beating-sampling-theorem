import BstLean.Part264bFrames1
namespace BstLean.Part264b
open Set
noncomputable def frameShard1 (n : ℕ) (hn : n ∈ Icc 12250 12274) : FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12250.frameData12250
  · exact N12251.frameData12251
  · exact N12252.frameData12252
  · exact N12253.frameData12253
  · exact N12254.frameData12254
  · exact N12255.frameData12255
  · exact N12256.frameData12256
  · exact N12257.frameData12257
  · exact N12258.frameData12258
  · exact N12259.frameData12259
  · exact N12260.frameData12260
  · exact N12261.frameData12261
  · exact N12262.frameData12262
  · exact N12263.frameData12263
  · exact N12264.frameData12264
  · exact N12265.frameData12265
  · exact N12266.frameData12266
  · exact N12267.frameData12267
  · exact N12268.frameData12268
  · exact N12269.frameData12269
  · exact N12270.frameData12270
  · exact N12271.frameData12271
  · exact N12272.frameData12272
  · exact N12273.frameData12273
  · exact N12274.frameData12274
end BstLean.Part264b
