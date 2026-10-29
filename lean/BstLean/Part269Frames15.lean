import BstLean.Part269Frames15Step0
import BstLean.Part269Frames15Step1
import BstLean.Part269Frames15Step2
import BstLean.Part269Frames15Step3
import BstLean.Part269Frames15Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard15 (n : ℕ) (hn : n ∈ Icc 12725 12749) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12725.frameData12725
  · exact N12726.frameData12726
  · exact N12727.frameData12727
  · exact N12728.frameData12728
  · exact N12729.frameData12729
  · exact N12730.frameData12730
  · exact N12731.frameData12731
  · exact N12732.frameData12732
  · exact N12733.frameData12733
  · exact N12734.frameData12734
  · exact N12735.frameData12735
  · exact N12736.frameData12736
  · exact N12737.frameData12737
  · exact N12738.frameData12738
  · exact N12739.frameData12739
  · exact N12740.frameData12740
  · exact N12741.frameData12741
  · exact N12742.frameData12742
  · exact N12743.frameData12743
  · exact N12744.frameData12744
  · exact N12745.frameData12745
  · exact N12746.frameData12746
  · exact N12747.frameData12747
  · exact N12748.frameData12748
  · exact N12749.frameData12749
end BstLean.Part269
