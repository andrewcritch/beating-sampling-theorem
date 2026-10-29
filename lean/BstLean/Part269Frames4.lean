import BstLean.Part269Frames4Step0
import BstLean.Part269Frames4Step1
import BstLean.Part269Frames4Step2
import BstLean.Part269Frames4Step3
import BstLean.Part269Frames4Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard4 (n : ℕ) (hn : n ∈ Icc 12450 12474) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12450.frameData12450
  · exact N12451.frameData12451
  · exact N12452.frameData12452
  · exact N12453.frameData12453
  · exact N12454.frameData12454
  · exact N12455.frameData12455
  · exact N12456.frameData12456
  · exact N12457.frameData12457
  · exact N12458.frameData12458
  · exact N12459.frameData12459
  · exact N12460.frameData12460
  · exact N12461.frameData12461
  · exact N12462.frameData12462
  · exact N12463.frameData12463
  · exact N12464.frameData12464
  · exact N12465.frameData12465
  · exact N12466.frameData12466
  · exact N12467.frameData12467
  · exact N12468.frameData12468
  · exact N12469.frameData12469
  · exact N12470.frameData12470
  · exact N12471.frameData12471
  · exact N12472.frameData12472
  · exact N12473.frameData12473
  · exact N12474.frameData12474
end BstLean.Part269
