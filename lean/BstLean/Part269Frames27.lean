import BstLean.Part269Frames27Step0
import BstLean.Part269Frames27Step1
import BstLean.Part269Frames27Step2
import BstLean.Part269Frames27Step3
import BstLean.Part269Frames27Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard27 (n : ℕ) (hn : n ∈ Icc 13025 13049) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13025.frameData13025
  · exact N13026.frameData13026
  · exact N13027.frameData13027
  · exact N13028.frameData13028
  · exact N13029.frameData13029
  · exact N13030.frameData13030
  · exact N13031.frameData13031
  · exact N13032.frameData13032
  · exact N13033.frameData13033
  · exact N13034.frameData13034
  · exact N13035.frameData13035
  · exact N13036.frameData13036
  · exact N13037.frameData13037
  · exact N13038.frameData13038
  · exact N13039.frameData13039
  · exact N13040.frameData13040
  · exact N13041.frameData13041
  · exact N13042.frameData13042
  · exact N13043.frameData13043
  · exact N13044.frameData13044
  · exact N13045.frameData13045
  · exact N13046.frameData13046
  · exact N13047.frameData13047
  · exact N13048.frameData13048
  · exact N13049.frameData13049
end BstLean.Part269
