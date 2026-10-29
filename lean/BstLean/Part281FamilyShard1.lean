import BstLean.Part281Rows1
namespace BstLean.Part281
open Real Set BstLean.Part130 BstLean.Part157
noncomputable def frameShard1 (n : ℕ) (hn : n ∈ Icc 11884 11908) : BstLean.Part264b.FrameData n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact N11884.frameData11884
  · exact N11885.frameData11885
  · exact N11886.frameData11886
  · exact N11887.frameData11887
  · exact N11888.frameData11888
  · exact N11889.frameData11889
  · exact N11890.frameData11890
  · exact N11891.frameData11891
  · exact N11892.frameData11892
  · exact N11893.frameData11893
  · exact N11894.frameData11894
  · exact N11895.frameData11895
  · exact N11896.frameData11896
  · exact N11897.frameData11897
  · exact N11898.frameData11898
  · exact N11899.frameData11899
  · exact N11900.frameData11900
  · exact N11901.frameData11901
  · exact N11902.frameData11902
  · exact N11903.frameData11903
  · exact N11904.frameData11904
  · exact N11905.frameData11905
  · exact N11906.frameData11906
  · exact N11907.frameData11907
  · exact N11908.frameData11908
noncomputable def rowShard1 (n : ℕ) (hn : n ∈ Icc 11884 11908) : BstLean.Part259.RowInputs n := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact row11884
  · exact row11885
  · exact row11886
  · exact row11887
  · exact row11888
  · exact row11889
  · exact row11890
  · exact row11891
  · exact row11892
  · exact row11893
  · exact row11894
  · exact row11895
  · exact row11896
  · exact row11897
  · exact row11898
  · exact row11899
  · exact row11900
  · exact row11901
  · exact row11902
  · exact row11903
  · exact row11904
  · exact row11905
  · exact row11906
  · exact row11907
  · exact row11908
theorem classifierShard1 (n : ℕ) (hn : n ∈ Icc 11884 11908) (t : ℝ) :
    99/100 ≤ ((mlpTriple 2 n).prod (sampMeas (10^12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
        BstLean.Part156.aL (10^12) x.1 x.2)} := by
  obtain ⟨hl,hu⟩ := hn
  interval_cases n
  · exact classifier_stated_11884 t
  · exact classifier_stated_11885 t
  · exact classifier_stated_11886 t
  · exact classifier_stated_11887 t
  · exact classifier_stated_11888 t
  · exact classifier_stated_11889 t
  · exact classifier_stated_11890 t
  · exact classifier_stated_11891 t
  · exact classifier_stated_11892 t
  · exact classifier_stated_11893 t
  · exact classifier_stated_11894 t
  · exact classifier_stated_11895 t
  · exact classifier_stated_11896 t
  · exact classifier_stated_11897 t
  · exact classifier_stated_11898 t
  · exact classifier_stated_11899 t
  · exact classifier_stated_11900 t
  · exact classifier_stated_11901 t
  · exact classifier_stated_11902 t
  · exact classifier_stated_11903 t
  · exact classifier_stated_11904 t
  · exact classifier_stated_11905 t
  · exact classifier_stated_11906 t
  · exact classifier_stated_11907 t
  · exact classifier_stated_11908 t
end BstLean.Part281
