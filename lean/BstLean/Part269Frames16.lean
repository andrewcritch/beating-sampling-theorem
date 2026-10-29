import BstLean.Part269Frames16Step0
import BstLean.Part269Frames16Step1
import BstLean.Part269Frames16Step2
import BstLean.Part269Frames16Step3
import BstLean.Part269Frames16Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard16 (n : ℕ) (hn : n ∈ Icc 12750 12774) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12750.frameData12750
  · exact N12751.frameData12751
  · exact N12752.frameData12752
  · exact N12753.frameData12753
  · exact N12754.frameData12754
  · exact N12755.frameData12755
  · exact N12756.frameData12756
  · exact N12757.frameData12757
  · exact N12758.frameData12758
  · exact N12759.frameData12759
  · exact N12760.frameData12760
  · exact N12761.frameData12761
  · exact N12762.frameData12762
  · exact N12763.frameData12763
  · exact N12764.frameData12764
  · exact N12765.frameData12765
  · exact N12766.frameData12766
  · exact N12767.frameData12767
  · exact N12768.frameData12768
  · exact N12769.frameData12769
  · exact N12770.frameData12770
  · exact N12771.frameData12771
  · exact N12772.frameData12772
  · exact N12773.frameData12773
  · exact N12774.frameData12774
end BstLean.Part269
