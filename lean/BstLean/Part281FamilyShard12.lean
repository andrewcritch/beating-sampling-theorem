import BstLean.Part281Rows12Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard12 (n : ℕ) (hn : n ∈ Icc 12159 12183) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12159.frameData12159
  · exact N12160.frameData12160
  · exact N12161.frameData12161
  · exact N12162.frameData12162
  · exact N12163.frameData12163
  · exact N12164.frameData12164
  · exact N12165.frameData12165
  · exact N12166.frameData12166
  · exact N12167.frameData12167
  · exact N12168.frameData12168
  · exact N12169.frameData12169
  · exact N12170.frameData12170
  · exact N12171.frameData12171
  · exact N12172.frameData12172
  · exact N12173.frameData12173
  · exact N12174.frameData12174
  · exact N12175.frameData12175
  · exact N12176.frameData12176
  · exact N12177.frameData12177
  · exact N12178.frameData12178
  · exact N12179.frameData12179
  · exact N12180.frameData12180
  · exact N12181.frameData12181
  · exact N12182.frameData12182
  · exact N12183.frameData12183
noncomputable def rowShard12 (n : ℕ) (hn : n ∈ Icc 12159 12183) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12159
  · exact row12160
  · exact row12161
  · exact row12162
  · exact row12163
  · exact row12164
  · exact row12165
  · exact row12166
  · exact row12167
  · exact row12168
  · exact row12169
  · exact row12170
  · exact row12171
  · exact row12172
  · exact row12173
  · exact row12174
  · exact row12175
  · exact row12176
  · exact row12177
  · exact row12178
  · exact row12179
  · exact row12180
  · exact row12181
  · exact row12182
  · exact row12183
theorem classifierShard12 (n : ℕ) (hn : n ∈ Icc 12159 12183) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12159 t
  · exact classifier_stated_12160 t
  · exact classifier_stated_12161 t
  · exact classifier_stated_12162 t
  · exact classifier_stated_12163 t
  · exact classifier_stated_12164 t
  · exact classifier_stated_12165 t
  · exact classifier_stated_12166 t
  · exact classifier_stated_12167 t
  · exact classifier_stated_12168 t
  · exact classifier_stated_12169 t
  · exact classifier_stated_12170 t
  · exact classifier_stated_12171 t
  · exact classifier_stated_12172 t
  · exact classifier_stated_12173 t
  · exact classifier_stated_12174 t
  · exact classifier_stated_12175 t
  · exact classifier_stated_12176 t
  · exact classifier_stated_12177 t
  · exact classifier_stated_12178 t
  · exact classifier_stated_12179 t
  · exact classifier_stated_12180 t
  · exact classifier_stated_12181 t
  · exact classifier_stated_12182 t
  · exact classifier_stated_12183 t
end BstLean.Part281
