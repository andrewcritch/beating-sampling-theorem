import BstLean.Part281Rows5
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard5 (n : ℕ) (hn : n ∈ Icc 11984 12008) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N11984.frameData11984
  · exact N11985.frameData11985
  · exact N11986.frameData11986
  · exact N11987.frameData11987
  · exact N11988.frameData11988
  · exact N11989.frameData11989
  · exact N11990.frameData11990
  · exact N11991.frameData11991
  · exact N11992.frameData11992
  · exact N11993.frameData11993
  · exact N11994.frameData11994
  · exact N11995.frameData11995
  · exact N11996.frameData11996
  · exact N11997.frameData11997
  · exact N11998.frameData11998
  · exact N11999.frameData11999
  · exact N12000.frameData12000
  · exact N12001.frameData12001
  · exact N12002.frameData12002
  · exact N12003.frameData12003
  · exact N12004.frameData12004
  · exact N12005.frameData12005
  · exact N12006.frameData12006
  · exact N12007.frameData12007
  · exact N12008.frameData12008
noncomputable def rowShard5 (n : ℕ) (hn : n ∈ Icc 11984 12008) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row11984
  · exact row11985
  · exact row11986
  · exact row11987
  · exact row11988
  · exact row11989
  · exact row11990
  · exact row11991
  · exact row11992
  · exact row11993
  · exact row11994
  · exact row11995
  · exact row11996
  · exact row11997
  · exact row11998
  · exact row11999
  · exact row12000
  · exact row12001
  · exact row12002
  · exact row12003
  · exact row12004
  · exact row12005
  · exact row12006
  · exact row12007
  · exact row12008
theorem classifierShard5 (n : ℕ) (hn : n ∈ Icc 11984 12008) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_11984 t
  · exact classifier_stated_11985 t
  · exact classifier_stated_11986 t
  · exact classifier_stated_11987 t
  · exact classifier_stated_11988 t
  · exact classifier_stated_11989 t
  · exact classifier_stated_11990 t
  · exact classifier_stated_11991 t
  · exact classifier_stated_11992 t
  · exact classifier_stated_11993 t
  · exact classifier_stated_11994 t
  · exact classifier_stated_11995 t
  · exact classifier_stated_11996 t
  · exact classifier_stated_11997 t
  · exact classifier_stated_11998 t
  · exact classifier_stated_11999 t
  · exact classifier_stated_12000 t
  · exact classifier_stated_12001 t
  · exact classifier_stated_12002 t
  · exact classifier_stated_12003 t
  · exact classifier_stated_12004 t
  · exact classifier_stated_12005 t
  · exact classifier_stated_12006 t
  · exact classifier_stated_12007 t
  · exact classifier_stated_12008 t
end BstLean.Part281
