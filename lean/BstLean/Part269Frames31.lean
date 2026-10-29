import BstLean.Part269Frames31Step0
import BstLean.Part269Frames31Step1
import BstLean.Part269Frames31Step2
import BstLean.Part269Frames31Step3
import BstLean.Part269Frames31Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard31 (n : ℕ) (hn : n ∈ Icc 13125 13149) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N13125.frameData13125
  · exact N13126.frameData13126
  · exact N13127.frameData13127
  · exact N13128.frameData13128
  · exact N13129.frameData13129
  · exact N13130.frameData13130
  · exact N13131.frameData13131
  · exact N13132.frameData13132
  · exact N13133.frameData13133
  · exact N13134.frameData13134
  · exact N13135.frameData13135
  · exact N13136.frameData13136
  · exact N13137.frameData13137
  · exact N13138.frameData13138
  · exact N13139.frameData13139
  · exact N13140.frameData13140
  · exact N13141.frameData13141
  · exact N13142.frameData13142
  · exact N13143.frameData13143
  · exact N13144.frameData13144
  · exact N13145.frameData13145
  · exact N13146.frameData13146
  · exact N13147.frameData13147
  · exact N13148.frameData13148
  · exact N13149.frameData13149
end BstLean.Part269
