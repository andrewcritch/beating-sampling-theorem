import BstLean.Part269Frames25Step0
import BstLean.Part269Frames25Step1
import BstLean.Part269Frames25Step2
import BstLean.Part269Frames25Step3
import BstLean.Part269Frames25Step4
namespace BstLean.Part269
open Set
noncomputable def frameShard25 (n : ℕ) (hn : n ∈ Icc 12975 12999) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12975.frameData12975
  · exact N12976.frameData12976
  · exact N12977.frameData12977
  · exact N12978.frameData12978
  · exact N12979.frameData12979
  · exact N12980.frameData12980
  · exact N12981.frameData12981
  · exact N12982.frameData12982
  · exact N12983.frameData12983
  · exact N12984.frameData12984
  · exact N12985.frameData12985
  · exact N12986.frameData12986
  · exact N12987.frameData12987
  · exact N12988.frameData12988
  · exact N12989.frameData12989
  · exact N12990.frameData12990
  · exact N12991.frameData12991
  · exact N12992.frameData12992
  · exact N12993.frameData12993
  · exact N12994.frameData12994
  · exact N12995.frameData12995
  · exact N12996.frameData12996
  · exact N12997.frameData12997
  · exact N12998.frameData12998
  · exact N12999.frameData12999
end BstLean.Part269
