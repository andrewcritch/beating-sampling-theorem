import BstLean.Part269Frames24Step0
import BstLean.Part269Frames24Step1
import BstLean.Part269Frames24Step2
import BstLean.Part269Frames24Step3
import BstLean.Part269Frames24Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard24 (n : ℕ) (hn : n ∈ Icc 12950 12974) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12950.frameData12950
  · exact N12951.frameData12951
  · exact N12952.frameData12952
  · exact N12953.frameData12953
  · exact N12954.frameData12954
  · exact N12955.frameData12955
  · exact N12956.frameData12956
  · exact N12957.frameData12957
  · exact N12958.frameData12958
  · exact N12959.frameData12959
  · exact N12960.frameData12960
  · exact N12961.frameData12961
  · exact N12962.frameData12962
  · exact N12963.frameData12963
  · exact N12964.frameData12964
  · exact N12965.frameData12965
  · exact N12966.frameData12966
  · exact N12967.frameData12967
  · exact N12968.frameData12968
  · exact N12969.frameData12969
  · exact N12970.frameData12970
  · exact N12971.frameData12971
  · exact N12972.frameData12972
  · exact N12973.frameData12973
  · exact N12974.frameData12974
end BstLean.Part269
