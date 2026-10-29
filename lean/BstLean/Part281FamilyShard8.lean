import BstLean.Part281Rows8Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard8 (n : ℕ) (hn : n ∈ Icc 12059 12083) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12059.frameData12059
  · exact N12060.frameData12060
  · exact N12061.frameData12061
  · exact N12062.frameData12062
  · exact N12063.frameData12063
  · exact N12064.frameData12064
  · exact N12065.frameData12065
  · exact N12066.frameData12066
  · exact N12067.frameData12067
  · exact N12068.frameData12068
  · exact N12069.frameData12069
  · exact N12070.frameData12070
  · exact N12071.frameData12071
  · exact N12072.frameData12072
  · exact N12073.frameData12073
  · exact N12074.frameData12074
  · exact N12075.frameData12075
  · exact N12076.frameData12076
  · exact N12077.frameData12077
  · exact N12078.frameData12078
  · exact N12079.frameData12079
  · exact N12080.frameData12080
  · exact N12081.frameData12081
  · exact N12082.frameData12082
  · exact N12083.frameData12083
noncomputable def rowShard8 (n : ℕ) (hn : n ∈ Icc 12059 12083) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12059
  · exact row12060
  · exact row12061
  · exact row12062
  · exact row12063
  · exact row12064
  · exact row12065
  · exact row12066
  · exact row12067
  · exact row12068
  · exact row12069
  · exact row12070
  · exact row12071
  · exact row12072
  · exact row12073
  · exact row12074
  · exact row12075
  · exact row12076
  · exact row12077
  · exact row12078
  · exact row12079
  · exact row12080
  · exact row12081
  · exact row12082
  · exact row12083
theorem classifierShard8 (n : ℕ) (hn : n ∈ Icc 12059 12083) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12059 t
  · exact classifier_stated_12060 t
  · exact classifier_stated_12061 t
  · exact classifier_stated_12062 t
  · exact classifier_stated_12063 t
  · exact classifier_stated_12064 t
  · exact classifier_stated_12065 t
  · exact classifier_stated_12066 t
  · exact classifier_stated_12067 t
  · exact classifier_stated_12068 t
  · exact classifier_stated_12069 t
  · exact classifier_stated_12070 t
  · exact classifier_stated_12071 t
  · exact classifier_stated_12072 t
  · exact classifier_stated_12073 t
  · exact classifier_stated_12074 t
  · exact classifier_stated_12075 t
  · exact classifier_stated_12076 t
  · exact classifier_stated_12077 t
  · exact classifier_stated_12078 t
  · exact classifier_stated_12079 t
  · exact classifier_stated_12080 t
  · exact classifier_stated_12081 t
  · exact classifier_stated_12082 t
  · exact classifier_stated_12083 t
end BstLean.Part281
