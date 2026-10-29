import BstLean.Part281Rows3Step1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard3 (n : ℕ) (hn : n ∈ Icc 11934 11958) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N11934.frameData11934
  · exact N11935.frameData11935
  · exact N11936.frameData11936
  · exact N11937.frameData11937
  · exact N11938.frameData11938
  · exact N11939.frameData11939
  · exact N11940.frameData11940
  · exact N11941.frameData11941
  · exact N11942.frameData11942
  · exact N11943.frameData11943
  · exact N11944.frameData11944
  · exact N11945.frameData11945
  · exact N11946.frameData11946
  · exact N11947.frameData11947
  · exact N11948.frameData11948
  · exact N11949.frameData11949
  · exact N11950.frameData11950
  · exact N11951.frameData11951
  · exact N11952.frameData11952
  · exact N11953.frameData11953
  · exact N11954.frameData11954
  · exact N11955.frameData11955
  · exact N11956.frameData11956
  · exact N11957.frameData11957
  · exact N11958.frameData11958
noncomputable def rowShard3 (n : ℕ) (hn : n ∈ Icc 11934 11958) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row11934
  · exact row11935
  · exact row11936
  · exact row11937
  · exact row11938
  · exact row11939
  · exact row11940
  · exact row11941
  · exact row11942
  · exact row11943
  · exact row11944
  · exact row11945
  · exact row11946
  · exact row11947
  · exact row11948
  · exact row11949
  · exact row11950
  · exact row11951
  · exact row11952
  · exact row11953
  · exact row11954
  · exact row11955
  · exact row11956
  · exact row11957
  · exact row11958
theorem classifierShard3 (n : ℕ) (hn : n ∈ Icc 11934 11958) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_11934 t
  · exact classifier_stated_11935 t
  · exact classifier_stated_11936 t
  · exact classifier_stated_11937 t
  · exact classifier_stated_11938 t
  · exact classifier_stated_11939 t
  · exact classifier_stated_11940 t
  · exact classifier_stated_11941 t
  · exact classifier_stated_11942 t
  · exact classifier_stated_11943 t
  · exact classifier_stated_11944 t
  · exact classifier_stated_11945 t
  · exact classifier_stated_11946 t
  · exact classifier_stated_11947 t
  · exact classifier_stated_11948 t
  · exact classifier_stated_11949 t
  · exact classifier_stated_11950 t
  · exact classifier_stated_11951 t
  · exact classifier_stated_11952 t
  · exact classifier_stated_11953 t
  · exact classifier_stated_11954 t
  · exact classifier_stated_11955 t
  · exact classifier_stated_11956 t
  · exact classifier_stated_11957 t
  · exact classifier_stated_11958 t
end BstLean.Part281
