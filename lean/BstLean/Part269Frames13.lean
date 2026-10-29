import BstLean.Part269Frames13Step0
import BstLean.Part269Frames13Step1
import BstLean.Part269Frames13Step2
import BstLean.Part269Frames13Step3
import BstLean.Part269Frames13Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard13 (n : ℕ) (hn : n ∈ Icc 12675 12699) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12675.frameData12675
  · exact N12676.frameData12676
  · exact N12677.frameData12677
  · exact N12678.frameData12678
  · exact N12679.frameData12679
  · exact N12680.frameData12680
  · exact N12681.frameData12681
  · exact N12682.frameData12682
  · exact N12683.frameData12683
  · exact N12684.frameData12684
  · exact N12685.frameData12685
  · exact N12686.frameData12686
  · exact N12687.frameData12687
  · exact N12688.frameData12688
  · exact N12689.frameData12689
  · exact N12690.frameData12690
  · exact N12691.frameData12691
  · exact N12692.frameData12692
  · exact N12693.frameData12693
  · exact N12694.frameData12694
  · exact N12695.frameData12695
  · exact N12696.frameData12696
  · exact N12697.frameData12697
  · exact N12698.frameData12698
  · exact N12699.frameData12699
end BstLean.Part269
