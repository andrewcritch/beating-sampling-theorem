import BstLean.Part269Frames3Step0
import BstLean.Part269Frames3Step1
import BstLean.Part269Frames3Step2
import BstLean.Part269Frames3Step3
import BstLean.Part269Frames3Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard3 (n : ℕ) (hn : n ∈ Icc 12425 12449) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12425.frameData12425
  · exact N12426.frameData12426
  · exact N12427.frameData12427
  · exact N12428.frameData12428
  · exact N12429.frameData12429
  · exact N12430.frameData12430
  · exact N12431.frameData12431
  · exact N12432.frameData12432
  · exact N12433.frameData12433
  · exact N12434.frameData12434
  · exact N12435.frameData12435
  · exact N12436.frameData12436
  · exact N12437.frameData12437
  · exact N12438.frameData12438
  · exact N12439.frameData12439
  · exact N12440.frameData12440
  · exact N12441.frameData12441
  · exact N12442.frameData12442
  · exact N12443.frameData12443
  · exact N12444.frameData12444
  · exact N12445.frameData12445
  · exact N12446.frameData12446
  · exact N12447.frameData12447
  · exact N12448.frameData12448
  · exact N12449.frameData12449
end BstLean.Part269
