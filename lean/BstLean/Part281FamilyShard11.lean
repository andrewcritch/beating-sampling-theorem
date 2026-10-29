import BstLean.Part281Rows11Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard11 (n : ℕ) (hn : n ∈ Icc 12134 12158) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12134.frameData12134
  · exact N12135.frameData12135
  · exact N12136.frameData12136
  · exact N12137.frameData12137
  · exact N12138.frameData12138
  · exact N12139.frameData12139
  · exact N12140.frameData12140
  · exact N12141.frameData12141
  · exact N12142.frameData12142
  · exact N12143.frameData12143
  · exact N12144.frameData12144
  · exact N12145.frameData12145
  · exact N12146.frameData12146
  · exact N12147.frameData12147
  · exact N12148.frameData12148
  · exact N12149.frameData12149
  · exact N12150.frameData12150
  · exact N12151.frameData12151
  · exact N12152.frameData12152
  · exact N12153.frameData12153
  · exact N12154.frameData12154
  · exact N12155.frameData12155
  · exact N12156.frameData12156
  · exact N12157.frameData12157
  · exact N12158.frameData12158
noncomputable def rowShard11 (n : ℕ) (hn : n ∈ Icc 12134 12158) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12134
  · exact row12135
  · exact row12136
  · exact row12137
  · exact row12138
  · exact row12139
  · exact row12140
  · exact row12141
  · exact row12142
  · exact row12143
  · exact row12144
  · exact row12145
  · exact row12146
  · exact row12147
  · exact row12148
  · exact row12149
  · exact row12150
  · exact row12151
  · exact row12152
  · exact row12153
  · exact row12154
  · exact row12155
  · exact row12156
  · exact row12157
  · exact row12158
theorem classifierShard11 (n : ℕ) (hn : n ∈ Icc 12134 12158) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12134 t
  · exact classifier_stated_12135 t
  · exact classifier_stated_12136 t
  · exact classifier_stated_12137 t
  · exact classifier_stated_12138 t
  · exact classifier_stated_12139 t
  · exact classifier_stated_12140 t
  · exact classifier_stated_12141 t
  · exact classifier_stated_12142 t
  · exact classifier_stated_12143 t
  · exact classifier_stated_12144 t
  · exact classifier_stated_12145 t
  · exact classifier_stated_12146 t
  · exact classifier_stated_12147 t
  · exact classifier_stated_12148 t
  · exact classifier_stated_12149 t
  · exact classifier_stated_12150 t
  · exact classifier_stated_12151 t
  · exact classifier_stated_12152 t
  · exact classifier_stated_12153 t
  · exact classifier_stated_12154 t
  · exact classifier_stated_12155 t
  · exact classifier_stated_12156 t
  · exact classifier_stated_12157 t
  · exact classifier_stated_12158 t
end BstLean.Part281
