import BstLean.Part281Rows9
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard9 (n : ℕ) (hn : n ∈ Icc 12084 12108) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12084.frameData12084
  · exact N12085.frameData12085
  · exact N12086.frameData12086
  · exact N12087.frameData12087
  · exact N12088.frameData12088
  · exact N12089.frameData12089
  · exact N12090.frameData12090
  · exact N12091.frameData12091
  · exact N12092.frameData12092
  · exact N12093.frameData12093
  · exact N12094.frameData12094
  · exact N12095.frameData12095
  · exact N12096.frameData12096
  · exact N12097.frameData12097
  · exact N12098.frameData12098
  · exact N12099.frameData12099
  · exact N12100.frameData12100
  · exact N12101.frameData12101
  · exact N12102.frameData12102
  · exact N12103.frameData12103
  · exact N12104.frameData12104
  · exact N12105.frameData12105
  · exact N12106.frameData12106
  · exact N12107.frameData12107
  · exact N12108.frameData12108
noncomputable def rowShard9 (n : ℕ) (hn : n ∈ Icc 12084 12108) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12084
  · exact row12085
  · exact row12086
  · exact row12087
  · exact row12088
  · exact row12089
  · exact row12090
  · exact row12091
  · exact row12092
  · exact row12093
  · exact row12094
  · exact row12095
  · exact row12096
  · exact row12097
  · exact row12098
  · exact row12099
  · exact row12100
  · exact row12101
  · exact row12102
  · exact row12103
  · exact row12104
  · exact row12105
  · exact row12106
  · exact row12107
  · exact row12108
theorem classifierShard9 (n : ℕ) (hn : n ∈ Icc 12084 12108) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12084 t
  · exact classifier_stated_12085 t
  · exact classifier_stated_12086 t
  · exact classifier_stated_12087 t
  · exact classifier_stated_12088 t
  · exact classifier_stated_12089 t
  · exact classifier_stated_12090 t
  · exact classifier_stated_12091 t
  · exact classifier_stated_12092 t
  · exact classifier_stated_12093 t
  · exact classifier_stated_12094 t
  · exact classifier_stated_12095 t
  · exact classifier_stated_12096 t
  · exact classifier_stated_12097 t
  · exact classifier_stated_12098 t
  · exact classifier_stated_12099 t
  · exact classifier_stated_12100 t
  · exact classifier_stated_12101 t
  · exact classifier_stated_12102 t
  · exact classifier_stated_12103 t
  · exact classifier_stated_12104 t
  · exact classifier_stated_12105 t
  · exact classifier_stated_12106 t
  · exact classifier_stated_12107 t
  · exact classifier_stated_12108 t
end BstLean.Part281
