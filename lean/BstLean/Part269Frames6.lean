import BstLean.Part269Frames6Step0
import BstLean.Part269Frames6Step1
import BstLean.Part269Frames6Step2
import BstLean.Part269Frames6Step3
import BstLean.Part269Frames6Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard6 (n : ℕ) (hn : n ∈ Icc 12500 12524) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12500.frameData12500
  · exact N12501.frameData12501
  · exact N12502.frameData12502
  · exact N12503.frameData12503
  · exact N12504.frameData12504
  · exact N12505.frameData12505
  · exact N12506.frameData12506
  · exact N12507.frameData12507
  · exact N12508.frameData12508
  · exact N12509.frameData12509
  · exact N12510.frameData12510
  · exact N12511.frameData12511
  · exact N12512.frameData12512
  · exact N12513.frameData12513
  · exact N12514.frameData12514
  · exact N12515.frameData12515
  · exact N12516.frameData12516
  · exact N12517.frameData12517
  · exact N12518.frameData12518
  · exact N12519.frameData12519
  · exact N12520.frameData12520
  · exact N12521.frameData12521
  · exact N12522.frameData12522
  · exact N12523.frameData12523
  · exact N12524.frameData12524
end BstLean.Part269
