import BstLean.Part269Frames20Step0
import BstLean.Part269Frames20Step1
import BstLean.Part269Frames20Step2
import BstLean.Part269Frames20Step3
import BstLean.Part269Frames20Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard20 (n : ℕ) (hn : n ∈ Icc 12850 12874) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12850.frameData12850
  · exact N12851.frameData12851
  · exact N12852.frameData12852
  · exact N12853.frameData12853
  · exact N12854.frameData12854
  · exact N12855.frameData12855
  · exact N12856.frameData12856
  · exact N12857.frameData12857
  · exact N12858.frameData12858
  · exact N12859.frameData12859
  · exact N12860.frameData12860
  · exact N12861.frameData12861
  · exact N12862.frameData12862
  · exact N12863.frameData12863
  · exact N12864.frameData12864
  · exact N12865.frameData12865
  · exact N12866.frameData12866
  · exact N12867.frameData12867
  · exact N12868.frameData12868
  · exact N12869.frameData12869
  · exact N12870.frameData12870
  · exact N12871.frameData12871
  · exact N12872.frameData12872
  · exact N12873.frameData12873
  · exact N12874.frameData12874
end BstLean.Part269
