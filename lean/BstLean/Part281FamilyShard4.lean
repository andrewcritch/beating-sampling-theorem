import BstLean.Part281Rows4Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard4 (n : ℕ) (hn : n ∈ Icc 11959 11983) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N11959.frameData11959
  · exact N11960.frameData11960
  · exact N11961.frameData11961
  · exact N11962.frameData11962
  · exact N11963.frameData11963
  · exact N11964.frameData11964
  · exact N11965.frameData11965
  · exact N11966.frameData11966
  · exact N11967.frameData11967
  · exact N11968.frameData11968
  · exact N11969.frameData11969
  · exact N11970.frameData11970
  · exact N11971.frameData11971
  · exact N11972.frameData11972
  · exact N11973.frameData11973
  · exact N11974.frameData11974
  · exact N11975.frameData11975
  · exact N11976.frameData11976
  · exact N11977.frameData11977
  · exact N11978.frameData11978
  · exact N11979.frameData11979
  · exact N11980.frameData11980
  · exact N11981.frameData11981
  · exact N11982.frameData11982
  · exact N11983.frameData11983
noncomputable def rowShard4 (n : ℕ) (hn : n ∈ Icc 11959 11983) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row11959
  · exact row11960
  · exact row11961
  · exact row11962
  · exact row11963
  · exact row11964
  · exact row11965
  · exact row11966
  · exact row11967
  · exact row11968
  · exact row11969
  · exact row11970
  · exact row11971
  · exact row11972
  · exact row11973
  · exact row11974
  · exact row11975
  · exact row11976
  · exact row11977
  · exact row11978
  · exact row11979
  · exact row11980
  · exact row11981
  · exact row11982
  · exact row11983
theorem classifierShard4 (n : ℕ) (hn : n ∈ Icc 11959 11983) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_11959 t
  · exact classifier_stated_11960 t
  · exact classifier_stated_11961 t
  · exact classifier_stated_11962 t
  · exact classifier_stated_11963 t
  · exact classifier_stated_11964 t
  · exact classifier_stated_11965 t
  · exact classifier_stated_11966 t
  · exact classifier_stated_11967 t
  · exact classifier_stated_11968 t
  · exact classifier_stated_11969 t
  · exact classifier_stated_11970 t
  · exact classifier_stated_11971 t
  · exact classifier_stated_11972 t
  · exact classifier_stated_11973 t
  · exact classifier_stated_11974 t
  · exact classifier_stated_11975 t
  · exact classifier_stated_11976 t
  · exact classifier_stated_11977 t
  · exact classifier_stated_11978 t
  · exact classifier_stated_11979 t
  · exact classifier_stated_11980 t
  · exact classifier_stated_11981 t
  · exact classifier_stated_11982 t
  · exact classifier_stated_11983 t
end BstLean.Part281
