import BstLean.Part269Frames2Step0
import BstLean.Part269Frames2Step1
import BstLean.Part269Frames2Step2
import BstLean.Part269Frames2Step3
import BstLean.Part269Frames2Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard2 (n : ℕ) (hn : n ∈ Icc 12400 12424) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12400.frameData12400
  · exact N12401.frameData12401
  · exact N12402.frameData12402
  · exact N12403.frameData12403
  · exact N12404.frameData12404
  · exact N12405.frameData12405
  · exact N12406.frameData12406
  · exact N12407.frameData12407
  · exact N12408.frameData12408
  · exact N12409.frameData12409
  · exact N12410.frameData12410
  · exact N12411.frameData12411
  · exact N12412.frameData12412
  · exact N12413.frameData12413
  · exact N12414.frameData12414
  · exact N12415.frameData12415
  · exact N12416.frameData12416
  · exact N12417.frameData12417
  · exact N12418.frameData12418
  · exact N12419.frameData12419
  · exact N12420.frameData12420
  · exact N12421.frameData12421
  · exact N12422.frameData12422
  · exact N12423.frameData12423
  · exact N12424.frameData12424
end BstLean.Part269
