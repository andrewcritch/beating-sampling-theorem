import BstLean.Part281Rows7Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard7 (n : ℕ) (hn : n ∈ Icc 12034 12058) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12034.frameData12034
  · exact N12035.frameData12035
  · exact N12036.frameData12036
  · exact N12037.frameData12037
  · exact N12038.frameData12038
  · exact N12039.frameData12039
  · exact N12040.frameData12040
  · exact N12041.frameData12041
  · exact N12042.frameData12042
  · exact N12043.frameData12043
  · exact N12044.frameData12044
  · exact N12045.frameData12045
  · exact N12046.frameData12046
  · exact N12047.frameData12047
  · exact N12048.frameData12048
  · exact N12049.frameData12049
  · exact N12050.frameData12050
  · exact N12051.frameData12051
  · exact N12052.frameData12052
  · exact N12053.frameData12053
  · exact N12054.frameData12054
  · exact N12055.frameData12055
  · exact N12056.frameData12056
  · exact N12057.frameData12057
  · exact N12058.frameData12058
noncomputable def rowShard7 (n : ℕ) (hn : n ∈ Icc 12034 12058) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12034
  · exact row12035
  · exact row12036
  · exact row12037
  · exact row12038
  · exact row12039
  · exact row12040
  · exact row12041
  · exact row12042
  · exact row12043
  · exact row12044
  · exact row12045
  · exact row12046
  · exact row12047
  · exact row12048
  · exact row12049
  · exact row12050
  · exact row12051
  · exact row12052
  · exact row12053
  · exact row12054
  · exact row12055
  · exact row12056
  · exact row12057
  · exact row12058
theorem classifierShard7 (n : ℕ) (hn : n ∈ Icc 12034 12058) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12034 t
  · exact classifier_stated_12035 t
  · exact classifier_stated_12036 t
  · exact classifier_stated_12037 t
  · exact classifier_stated_12038 t
  · exact classifier_stated_12039 t
  · exact classifier_stated_12040 t
  · exact classifier_stated_12041 t
  · exact classifier_stated_12042 t
  · exact classifier_stated_12043 t
  · exact classifier_stated_12044 t
  · exact classifier_stated_12045 t
  · exact classifier_stated_12046 t
  · exact classifier_stated_12047 t
  · exact classifier_stated_12048 t
  · exact classifier_stated_12049 t
  · exact classifier_stated_12050 t
  · exact classifier_stated_12051 t
  · exact classifier_stated_12052 t
  · exact classifier_stated_12053 t
  · exact classifier_stated_12054 t
  · exact classifier_stated_12055 t
  · exact classifier_stated_12056 t
  · exact classifier_stated_12057 t
  · exact classifier_stated_12058 t
end BstLean.Part281
