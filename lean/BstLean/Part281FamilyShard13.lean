import BstLean.Part281Rows13Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard13 (n : ℕ) (hn : n ∈ Icc 12184 12208) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12184.frameData12184
  · exact N12185.frameData12185
  · exact N12186.frameData12186
  · exact N12187.frameData12187
  · exact N12188.frameData12188
  · exact N12189.frameData12189
  · exact N12190.frameData12190
  · exact N12191.frameData12191
  · exact N12192.frameData12192
  · exact N12193.frameData12193
  · exact N12194.frameData12194
  · exact N12195.frameData12195
  · exact N12196.frameData12196
  · exact N12197.frameData12197
  · exact N12198.frameData12198
  · exact N12199.frameData12199
  · exact N12200.frameData12200
  · exact N12201.frameData12201
  · exact N12202.frameData12202
  · exact N12203.frameData12203
  · exact N12204.frameData12204
  · exact N12205.frameData12205
  · exact N12206.frameData12206
  · exact N12207.frameData12207
  · exact N12208.frameData12208
noncomputable def rowShard13 (n : ℕ) (hn : n ∈ Icc 12184 12208) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12184
  · exact row12185
  · exact row12186
  · exact row12187
  · exact row12188
  · exact row12189
  · exact row12190
  · exact row12191
  · exact row12192
  · exact row12193
  · exact row12194
  · exact row12195
  · exact row12196
  · exact row12197
  · exact row12198
  · exact row12199
  · exact row12200
  · exact row12201
  · exact row12202
  · exact row12203
  · exact row12204
  · exact row12205
  · exact row12206
  · exact row12207
  · exact row12208
theorem classifierShard13 (n : ℕ) (hn : n ∈ Icc 12184 12208) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12184 t
  · exact classifier_stated_12185 t
  · exact classifier_stated_12186 t
  · exact classifier_stated_12187 t
  · exact classifier_stated_12188 t
  · exact classifier_stated_12189 t
  · exact classifier_stated_12190 t
  · exact classifier_stated_12191 t
  · exact classifier_stated_12192 t
  · exact classifier_stated_12193 t
  · exact classifier_stated_12194 t
  · exact classifier_stated_12195 t
  · exact classifier_stated_12196 t
  · exact classifier_stated_12197 t
  · exact classifier_stated_12198 t
  · exact classifier_stated_12199 t
  · exact classifier_stated_12200 t
  · exact classifier_stated_12201 t
  · exact classifier_stated_12202 t
  · exact classifier_stated_12203 t
  · exact classifier_stated_12204 t
  · exact classifier_stated_12205 t
  · exact classifier_stated_12206 t
  · exact classifier_stated_12207 t
  · exact classifier_stated_12208 t
end BstLean.Part281
