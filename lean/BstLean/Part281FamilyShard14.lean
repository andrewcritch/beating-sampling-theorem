import BstLean.Part281Rows14Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard14 (n : ℕ) (hn : n ∈ Icc 12209 12223) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12209.frameData12209
  · exact N12210.frameData12210
  · exact N12211.frameData12211
  · exact N12212.frameData12212
  · exact N12213.frameData12213
  · exact N12214.frameData12214
  · exact N12215.frameData12215
  · exact N12216.frameData12216
  · exact N12217.frameData12217
  · exact N12218.frameData12218
  · exact N12219.frameData12219
  · exact N12220.frameData12220
  · exact N12221.frameData12221
  · exact N12222.frameData12222
  · exact N12223.frameData12223
noncomputable def rowShard14 (n : ℕ) (hn : n ∈ Icc 12209 12223) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12209
  · exact row12210
  · exact row12211
  · exact row12212
  · exact row12213
  · exact row12214
  · exact row12215
  · exact row12216
  · exact row12217
  · exact row12218
  · exact row12219
  · exact row12220
  · exact row12221
  · exact row12222
  · exact row12223
theorem classifierShard14 (n : ℕ) (hn : n ∈ Icc 12209 12223) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12209 t
  · exact classifier_stated_12210 t
  · exact classifier_stated_12211 t
  · exact classifier_stated_12212 t
  · exact classifier_stated_12213 t
  · exact classifier_stated_12214 t
  · exact classifier_stated_12215 t
  · exact classifier_stated_12216 t
  · exact classifier_stated_12217 t
  · exact classifier_stated_12218 t
  · exact classifier_stated_12219 t
  · exact classifier_stated_12220 t
  · exact classifier_stated_12221 t
  · exact classifier_stated_12222 t
  · exact classifier_stated_12223 t
end BstLean.Part281
