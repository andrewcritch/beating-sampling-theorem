import BstLean.Part269Frames1Step0
import BstLean.Part269Frames1Step1
import BstLean.Part269Frames1Step2
import BstLean.Part269Frames1Step3
import BstLean.Part269Frames1Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard1 (n : ℕ) (hn : n ∈ Icc 12375 12399) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12375.frameData12375
  · exact N12376.frameData12376
  · exact N12377.frameData12377
  · exact N12378.frameData12378
  · exact N12379.frameData12379
  · exact N12380.frameData12380
  · exact N12381.frameData12381
  · exact N12382.frameData12382
  · exact N12383.frameData12383
  · exact N12384.frameData12384
  · exact N12385.frameData12385
  · exact N12386.frameData12386
  · exact N12387.frameData12387
  · exact N12388.frameData12388
  · exact N12389.frameData12389
  · exact N12390.frameData12390
  · exact N12391.frameData12391
  · exact N12392.frameData12392
  · exact N12393.frameData12393
  · exact N12394.frameData12394
  · exact N12395.frameData12395
  · exact N12396.frameData12396
  · exact N12397.frameData12397
  · exact N12398.frameData12398
  · exact N12399.frameData12399
end BstLean.Part269
