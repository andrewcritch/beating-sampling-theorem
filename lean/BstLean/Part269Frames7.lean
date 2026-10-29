import BstLean.Part269Frames7Step0
import BstLean.Part269Frames7Step1
import BstLean.Part269Frames7Step2
import BstLean.Part269Frames7Step3
import BstLean.Part269Frames7Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard7 (n : ℕ) (hn : n ∈ Icc 12525 12549) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12525.frameData12525
  · exact N12526.frameData12526
  · exact N12527.frameData12527
  · exact N12528.frameData12528
  · exact N12529.frameData12529
  · exact N12530.frameData12530
  · exact N12531.frameData12531
  · exact N12532.frameData12532
  · exact N12533.frameData12533
  · exact N12534.frameData12534
  · exact N12535.frameData12535
  · exact N12536.frameData12536
  · exact N12537.frameData12537
  · exact N12538.frameData12538
  · exact N12539.frameData12539
  · exact N12540.frameData12540
  · exact N12541.frameData12541
  · exact N12542.frameData12542
  · exact N12543.frameData12543
  · exact N12544.frameData12544
  · exact N12545.frameData12545
  · exact N12546.frameData12546
  · exact N12547.frameData12547
  · exact N12548.frameData12548
  · exact N12549.frameData12549
end BstLean.Part269
