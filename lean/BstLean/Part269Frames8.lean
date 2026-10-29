import BstLean.Part269Frames8Step0
import BstLean.Part269Frames8Step1
import BstLean.Part269Frames8Step2
import BstLean.Part269Frames8Step3
import BstLean.Part269Frames8Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard8 (n : ℕ) (hn : n ∈ Icc 12550 12574) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12550.frameData12550
  · exact N12551.frameData12551
  · exact N12552.frameData12552
  · exact N12553.frameData12553
  · exact N12554.frameData12554
  · exact N12555.frameData12555
  · exact N12556.frameData12556
  · exact N12557.frameData12557
  · exact N12558.frameData12558
  · exact N12559.frameData12559
  · exact N12560.frameData12560
  · exact N12561.frameData12561
  · exact N12562.frameData12562
  · exact N12563.frameData12563
  · exact N12564.frameData12564
  · exact N12565.frameData12565
  · exact N12566.frameData12566
  · exact N12567.frameData12567
  · exact N12568.frameData12568
  · exact N12569.frameData12569
  · exact N12570.frameData12570
  · exact N12571.frameData12571
  · exact N12572.frameData12572
  · exact N12573.frameData12573
  · exact N12574.frameData12574
end BstLean.Part269
