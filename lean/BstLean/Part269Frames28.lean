import BstLean.Part269Frames28Step0
import BstLean.Part269Frames28Step1
import BstLean.Part269Frames28Step2
import BstLean.Part269Frames28Step3
import BstLean.Part269Frames28Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard28 (n : ℕ) (hn : n ∈ Icc 13050 13074) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13050.frameData13050
  · exact N13051.frameData13051
  · exact N13052.frameData13052
  · exact N13053.frameData13053
  · exact N13054.frameData13054
  · exact N13055.frameData13055
  · exact N13056.frameData13056
  · exact N13057.frameData13057
  · exact N13058.frameData13058
  · exact N13059.frameData13059
  · exact N13060.frameData13060
  · exact N13061.frameData13061
  · exact N13062.frameData13062
  · exact N13063.frameData13063
  · exact N13064.frameData13064
  · exact N13065.frameData13065
  · exact N13066.frameData13066
  · exact N13067.frameData13067
  · exact N13068.frameData13068
  · exact N13069.frameData13069
  · exact N13070.frameData13070
  · exact N13071.frameData13071
  · exact N13072.frameData13072
  · exact N13073.frameData13073
  · exact N13074.frameData13074
end BstLean.Part269
