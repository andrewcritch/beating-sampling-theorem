import BstLean.Part281Rows10Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard10 (n : ℕ) (hn : n ∈ Icc 12109 12133) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12109.frameData12109
  · exact N12110.frameData12110
  · exact N12111.frameData12111
  · exact N12112.frameData12112
  · exact N12113.frameData12113
  · exact N12114.frameData12114
  · exact N12115.frameData12115
  · exact N12116.frameData12116
  · exact N12117.frameData12117
  · exact N12118.frameData12118
  · exact N12119.frameData12119
  · exact N12120.frameData12120
  · exact N12121.frameData12121
  · exact N12122.frameData12122
  · exact N12123.frameData12123
  · exact N12124.frameData12124
  · exact N12125.frameData12125
  · exact N12126.frameData12126
  · exact N12127.frameData12127
  · exact N12128.frameData12128
  · exact N12129.frameData12129
  · exact N12130.frameData12130
  · exact N12131.frameData12131
  · exact N12132.frameData12132
  · exact N12133.frameData12133
noncomputable def rowShard10 (n : ℕ) (hn : n ∈ Icc 12109 12133) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12109
  · exact row12110
  · exact row12111
  · exact row12112
  · exact row12113
  · exact row12114
  · exact row12115
  · exact row12116
  · exact row12117
  · exact row12118
  · exact row12119
  · exact row12120
  · exact row12121
  · exact row12122
  · exact row12123
  · exact row12124
  · exact row12125
  · exact row12126
  · exact row12127
  · exact row12128
  · exact row12129
  · exact row12130
  · exact row12131
  · exact row12132
  · exact row12133
theorem classifierShard10 (n : ℕ) (hn : n ∈ Icc 12109 12133) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12109 t
  · exact classifier_stated_12110 t
  · exact classifier_stated_12111 t
  · exact classifier_stated_12112 t
  · exact classifier_stated_12113 t
  · exact classifier_stated_12114 t
  · exact classifier_stated_12115 t
  · exact classifier_stated_12116 t
  · exact classifier_stated_12117 t
  · exact classifier_stated_12118 t
  · exact classifier_stated_12119 t
  · exact classifier_stated_12120 t
  · exact classifier_stated_12121 t
  · exact classifier_stated_12122 t
  · exact classifier_stated_12123 t
  · exact classifier_stated_12124 t
  · exact classifier_stated_12125 t
  · exact classifier_stated_12126 t
  · exact classifier_stated_12127 t
  · exact classifier_stated_12128 t
  · exact classifier_stated_12129 t
  · exact classifier_stated_12130 t
  · exact classifier_stated_12131 t
  · exact classifier_stated_12132 t
  · exact classifier_stated_12133 t
end BstLean.Part281
