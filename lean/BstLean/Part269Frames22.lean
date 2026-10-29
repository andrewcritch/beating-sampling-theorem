import BstLean.Part269Frames22Step0
import BstLean.Part269Frames22Step1
import BstLean.Part269Frames22Step2
import BstLean.Part269Frames22Step3
import BstLean.Part269Frames22Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard22 (n : ℕ) (hn : n ∈ Icc 12900 12924) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12900.frameData12900
  · exact N12901.frameData12901
  · exact N12902.frameData12902
  · exact N12903.frameData12903
  · exact N12904.frameData12904
  · exact N12905.frameData12905
  · exact N12906.frameData12906
  · exact N12907.frameData12907
  · exact N12908.frameData12908
  · exact N12909.frameData12909
  · exact N12910.frameData12910
  · exact N12911.frameData12911
  · exact N12912.frameData12912
  · exact N12913.frameData12913
  · exact N12914.frameData12914
  · exact N12915.frameData12915
  · exact N12916.frameData12916
  · exact N12917.frameData12917
  · exact N12918.frameData12918
  · exact N12919.frameData12919
  · exact N12920.frameData12920
  · exact N12921.frameData12921
  · exact N12922.frameData12922
  · exact N12923.frameData12923
  · exact N12924.frameData12924
end BstLean.Part269
