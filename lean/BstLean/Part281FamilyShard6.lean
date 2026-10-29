import BstLean.Part281Rows6Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard6 (n : ℕ) (hn : n ∈ Icc 12009 12033) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N12009.frameData12009
  · exact N12010.frameData12010
  · exact N12011.frameData12011
  · exact N12012.frameData12012
  · exact N12013.frameData12013
  · exact N12014.frameData12014
  · exact N12015.frameData12015
  · exact N12016.frameData12016
  · exact N12017.frameData12017
  · exact N12018.frameData12018
  · exact N12019.frameData12019
  · exact N12020.frameData12020
  · exact N12021.frameData12021
  · exact N12022.frameData12022
  · exact N12023.frameData12023
  · exact N12024.frameData12024
  · exact N12025.frameData12025
  · exact N12026.frameData12026
  · exact N12027.frameData12027
  · exact N12028.frameData12028
  · exact N12029.frameData12029
  · exact N12030.frameData12030
  · exact N12031.frameData12031
  · exact N12032.frameData12032
  · exact N12033.frameData12033
noncomputable def rowShard6 (n : ℕ) (hn : n ∈ Icc 12009 12033) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row12009
  · exact row12010
  · exact row12011
  · exact row12012
  · exact row12013
  · exact row12014
  · exact row12015
  · exact row12016
  · exact row12017
  · exact row12018
  · exact row12019
  · exact row12020
  · exact row12021
  · exact row12022
  · exact row12023
  · exact row12024
  · exact row12025
  · exact row12026
  · exact row12027
  · exact row12028
  · exact row12029
  · exact row12030
  · exact row12031
  · exact row12032
  · exact row12033
theorem classifierShard6 (n : ℕ) (hn : n ∈ Icc 12009 12033) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_12009 t
  · exact classifier_stated_12010 t
  · exact classifier_stated_12011 t
  · exact classifier_stated_12012 t
  · exact classifier_stated_12013 t
  · exact classifier_stated_12014 t
  · exact classifier_stated_12015 t
  · exact classifier_stated_12016 t
  · exact classifier_stated_12017 t
  · exact classifier_stated_12018 t
  · exact classifier_stated_12019 t
  · exact classifier_stated_12020 t
  · exact classifier_stated_12021 t
  · exact classifier_stated_12022 t
  · exact classifier_stated_12023 t
  · exact classifier_stated_12024 t
  · exact classifier_stated_12025 t
  · exact classifier_stated_12026 t
  · exact classifier_stated_12027 t
  · exact classifier_stated_12028 t
  · exact classifier_stated_12029 t
  · exact classifier_stated_12030 t
  · exact classifier_stated_12031 t
  · exact classifier_stated_12032 t
  · exact classifier_stated_12033 t
end BstLean.Part281
