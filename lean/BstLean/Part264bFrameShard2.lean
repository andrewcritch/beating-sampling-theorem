import BstLean.Part264bFrames2
namespace BstLean.Part264b
open Set
noncomputable def frameShard2 (n : ℕ) (hn : n ∈ Icc 12275 12299) : FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12275.frameData12275
  · exact N12276.frameData12276
  · exact N12277.frameData12277
  · exact N12278.frameData12278
  · exact N12279.frameData12279
  · exact N12280.frameData12280
  · exact N12281.frameData12281
  · exact N12282.frameData12282
  · exact N12283.frameData12283
  · exact N12284.frameData12284
  · exact N12285.frameData12285
  · exact N12286.frameData12286
  · exact N12287.frameData12287
  · exact N12288.frameData12288
  · exact N12289.frameData12289
  · exact N12290.frameData12290
  · exact N12291.frameData12291
  · exact N12292.frameData12292
  · exact N12293.frameData12293
  · exact N12294.frameData12294
  · exact N12295.frameData12295
  · exact N12296.frameData12296
  · exact N12297.frameData12297
  · exact N12298.frameData12298
  · exact N12299.frameData12299
end BstLean.Part264b
