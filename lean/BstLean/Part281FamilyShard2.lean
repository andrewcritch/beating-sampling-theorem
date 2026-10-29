import BstLean.Part281Rows2Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard2 (n : ℕ) (hn : n ∈ Icc 11909 11933) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N11909.frameData11909
  · exact N11910.frameData11910
  · exact N11911.frameData11911
  · exact N11912.frameData11912
  · exact N11913.frameData11913
  · exact N11914.frameData11914
  · exact N11915.frameData11915
  · exact N11916.frameData11916
  · exact N11917.frameData11917
  · exact N11918.frameData11918
  · exact N11919.frameData11919
  · exact N11920.frameData11920
  · exact N11921.frameData11921
  · exact N11922.frameData11922
  · exact N11923.frameData11923
  · exact N11924.frameData11924
  · exact N11925.frameData11925
  · exact N11926.frameData11926
  · exact N11927.frameData11927
  · exact N11928.frameData11928
  · exact N11929.frameData11929
  · exact N11930.frameData11930
  · exact N11931.frameData11931
  · exact N11932.frameData11932
  · exact N11933.frameData11933
noncomputable def rowShard2 (n : ℕ) (hn : n ∈ Icc 11909 11933) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row11909
  · exact row11910
  · exact row11911
  · exact row11912
  · exact row11913
  · exact row11914
  · exact row11915
  · exact row11916
  · exact row11917
  · exact row11918
  · exact row11919
  · exact row11920
  · exact row11921
  · exact row11922
  · exact row11923
  · exact row11924
  · exact row11925
  · exact row11926
  · exact row11927
  · exact row11928
  · exact row11929
  · exact row11930
  · exact row11931
  · exact row11932
  · exact row11933
theorem classifierShard2 (n : ℕ) (hn : n ∈ Icc 11909 11933) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_11909 t
  · exact classifier_stated_11910 t
  · exact classifier_stated_11911 t
  · exact classifier_stated_11912 t
  · exact classifier_stated_11913 t
  · exact classifier_stated_11914 t
  · exact classifier_stated_11915 t
  · exact classifier_stated_11916 t
  · exact classifier_stated_11917 t
  · exact classifier_stated_11918 t
  · exact classifier_stated_11919 t
  · exact classifier_stated_11920 t
  · exact classifier_stated_11921 t
  · exact classifier_stated_11922 t
  · exact classifier_stated_11923 t
  · exact classifier_stated_11924 t
  · exact classifier_stated_11925 t
  · exact classifier_stated_11926 t
  · exact classifier_stated_11927 t
  · exact classifier_stated_11928 t
  · exact classifier_stated_11929 t
  · exact classifier_stated_11930 t
  · exact classifier_stated_11931 t
  · exact classifier_stated_11932 t
  · exact classifier_stated_11933 t
end BstLean.Part281
