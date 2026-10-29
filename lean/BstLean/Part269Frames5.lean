import BstLean.Part269Frames5Step0
import BstLean.Part269Frames5Step1
import BstLean.Part269Frames5Step2
import BstLean.Part269Frames5Step3
import BstLean.Part269Frames5Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard5 (n : ℕ) (hn : n ∈ Icc 12475 12499) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12475.frameData12475
  · exact N12476.frameData12476
  · exact N12477.frameData12477
  · exact N12478.frameData12478
  · exact N12479.frameData12479
  · exact N12480.frameData12480
  · exact N12481.frameData12481
  · exact N12482.frameData12482
  · exact N12483.frameData12483
  · exact N12484.frameData12484
  · exact N12485.frameData12485
  · exact N12486.frameData12486
  · exact N12487.frameData12487
  · exact N12488.frameData12488
  · exact N12489.frameData12489
  · exact N12490.frameData12490
  · exact N12491.frameData12491
  · exact N12492.frameData12492
  · exact N12493.frameData12493
  · exact N12494.frameData12494
  · exact N12495.frameData12495
  · exact N12496.frameData12496
  · exact N12497.frameData12497
  · exact N12498.frameData12498
  · exact N12499.frameData12499
end BstLean.Part269
