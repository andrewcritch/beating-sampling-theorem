import BstLean.Part269Frames23Step0
import BstLean.Part269Frames23Step1
import BstLean.Part269Frames23Step2
import BstLean.Part269Frames23Step3
import BstLean.Part269Frames23Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard23 (n : ℕ) (hn : n ∈ Icc 12925 12949) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12925.frameData12925
  · exact N12926.frameData12926
  · exact N12927.frameData12927
  · exact N12928.frameData12928
  · exact N12929.frameData12929
  · exact N12930.frameData12930
  · exact N12931.frameData12931
  · exact N12932.frameData12932
  · exact N12933.frameData12933
  · exact N12934.frameData12934
  · exact N12935.frameData12935
  · exact N12936.frameData12936
  · exact N12937.frameData12937
  · exact N12938.frameData12938
  · exact N12939.frameData12939
  · exact N12940.frameData12940
  · exact N12941.frameData12941
  · exact N12942.frameData12942
  · exact N12943.frameData12943
  · exact N12944.frameData12944
  · exact N12945.frameData12945
  · exact N12946.frameData12946
  · exact N12947.frameData12947
  · exact N12948.frameData12948
  · exact N12949.frameData12949
end BstLean.Part269
