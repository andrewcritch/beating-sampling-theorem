import BstLean.Part264bFrames3
namespace BstLean.Part264b
open Set
noncomputable def frameShard3 (n : ℕ) (hn : n ∈ Icc 12300 12324) : FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12300.frameData12300
  · exact N12301.frameData12301
  · exact N12302.frameData12302
  · exact N12303.frameData12303
  · exact N12304.frameData12304
  · exact N12305.frameData12305
  · exact N12306.frameData12306
  · exact N12307.frameData12307
  · exact N12308.frameData12308
  · exact N12309.frameData12309
  · exact N12310.frameData12310
  · exact N12311.frameData12311
  · exact N12312.frameData12312
  · exact N12313.frameData12313
  · exact N12314.frameData12314
  · exact N12315.frameData12315
  · exact N12316.frameData12316
  · exact N12317.frameData12317
  · exact N12318.frameData12318
  · exact N12319.frameData12319
  · exact N12320.frameData12320
  · exact N12321.frameData12321
  · exact N12322.frameData12322
  · exact N12323.frameData12323
  · exact N12324.frameData12324
end BstLean.Part264b
