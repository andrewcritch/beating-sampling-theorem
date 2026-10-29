import BstLean.Part291GeometryBatch3
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters112 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (59365081/500000000)
  cRadius := (32237281/500000000)

theorem lowTIParameters112_valid : Valid lowTIParameters112 := by
  constructor
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters112,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters112,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]
  · norm_num [lowTIParameters112]

theorem lowTISupply112 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters112 (129/250) (1033/2000) := by
  refine ⟨lowTIParameters112_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters112]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters112]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry112W hn hθ).1 (by norm_num [lowTIParameters112])
      (by norm_num [lowTIParameters112]) (by norm_num [lowTIParameters112])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry112C hn hθ).1 (by norm_num [lowTIParameters112])
      (by norm_num [lowTIParameters112]) (by norm_num [lowTIParameters112])
  · intro θ hθ
    exact (lowGeometry112W hn hθ).2
  · intro θ hθ
    exact (lowGeometry112C hn hθ).2

noncomputable def lowTIParameters113 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (29694487/250000000)
  cRadius := (12900949/200000000)

theorem lowTIParameters113_valid : Valid lowTIParameters113 := by
  constructor
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters113,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters113,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]
  · norm_num [lowTIParameters113]

theorem lowTISupply113 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters113 (1033/2000) (517/1000) := by
  refine ⟨lowTIParameters113_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters113]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters113]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry113W hn hθ).1 (by norm_num [lowTIParameters113])
      (by norm_num [lowTIParameters113]) (by norm_num [lowTIParameters113])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry113C hn hθ).1 (by norm_num [lowTIParameters113])
      (by norm_num [lowTIParameters113]) (by norm_num [lowTIParameters113])
  · intro θ hθ
    exact (lowGeometry113W hn hθ).2
  · intro θ hθ
    exact (lowGeometry113C hn hθ).2

noncomputable def lowTIParameters114 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (118825667/1000000000)
  cRadius := (12906979/200000000)

theorem lowTIParameters114_valid : Valid lowTIParameters114 := by
  constructor
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters114,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters114,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]
  · norm_num [lowTIParameters114]

theorem lowTISupply114 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters114 (517/1000) (207/400) := by
  refine ⟨lowTIParameters114_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters114]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters114]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry114W hn hθ).1 (by norm_num [lowTIParameters114])
      (by norm_num [lowTIParameters114]) (by norm_num [lowTIParameters114])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry114C hn hθ).1 (by norm_num [lowTIParameters114])
      (by norm_num [lowTIParameters114]) (by norm_num [lowTIParameters114])
  · intro θ hθ
    exact (lowGeometry114W hn hθ).2
  · intro θ hθ
    exact (lowGeometry114C hn hθ).2

noncomputable def lowTIParameters115 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (118873319/1000000000)
  cRadius := (64565013/1000000000)

theorem lowTIParameters115_valid : Valid lowTIParameters115 := by
  constructor
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters115,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters115,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]
  · norm_num [lowTIParameters115]

theorem lowTISupply115 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters115 (207/400) (259/500) := by
  refine ⟨lowTIParameters115_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters115]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters115]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry115W hn hθ).1 (by norm_num [lowTIParameters115])
      (by norm_num [lowTIParameters115]) (by norm_num [lowTIParameters115])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry115C hn hθ).1 (by norm_num [lowTIParameters115])
      (by norm_num [lowTIParameters115]) (by norm_num [lowTIParameters115])
  · intro θ hθ
    exact (lowGeometry115W hn hθ).2
  · intro θ hθ
    exact (lowGeometry115C hn hθ).2

noncomputable def lowTIParameters116 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (118920903/1000000000)
  cRadius := (32297549/500000000)

theorem lowTIParameters116_valid : Valid lowTIParameters116 := by
  constructor
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters116,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters116,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]
  · norm_num [lowTIParameters116]

theorem lowTISupply116 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters116 (259/500) (1037/2000) := by
  refine ⟨lowTIParameters116_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters116]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters116]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry116W hn hθ).1 (by norm_num [lowTIParameters116])
      (by norm_num [lowTIParameters116]) (by norm_num [lowTIParameters116])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry116C hn hθ).1 (by norm_num [lowTIParameters116])
      (by norm_num [lowTIParameters116]) (by norm_num [lowTIParameters116])
  · intro θ hθ
    exact (lowGeometry116W hn hθ).2
  · intro θ hθ
    exact (lowGeometry116C hn hθ).2

noncomputable def lowTIParameters117 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (118968421/1000000000)
  cRadius := (126221/1953125)

theorem lowTIParameters117_valid : Valid lowTIParameters117 := by
  constructor
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters117,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters117,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]
  · norm_num [lowTIParameters117]

theorem lowTISupply117 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters117 (1037/2000) (519/1000) := by
  refine ⟨lowTIParameters117_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters117]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters117]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry117W hn hθ).1 (by norm_num [lowTIParameters117])
      (by norm_num [lowTIParameters117]) (by norm_num [lowTIParameters117])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry117C hn hθ).1 (by norm_num [lowTIParameters117])
      (by norm_num [lowTIParameters117]) (by norm_num [lowTIParameters117])
  · intro θ hθ
    exact (lowGeometry117W hn hθ).2
  · intro θ hθ
    exact (lowGeometry117C hn hθ).2

noncomputable def lowTIParameters118 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (119015871/1000000000)
  cRadius := (64655173/1000000000)

theorem lowTIParameters118_valid : Valid lowTIParameters118 := by
  constructor
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters118,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters118,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]
  · norm_num [lowTIParameters118]

theorem lowTISupply118 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters118 (519/1000) (1039/2000) := by
  refine ⟨lowTIParameters118_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters118]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters118]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry118W hn hθ).1 (by norm_num [lowTIParameters118])
      (by norm_num [lowTIParameters118]) (by norm_num [lowTIParameters118])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry118C hn hθ).1 (by norm_num [lowTIParameters118])
      (by norm_num [lowTIParameters118]) (by norm_num [lowTIParameters118])
  · intro θ hθ
    exact (lowGeometry118W hn hθ).2
  · intro θ hθ
    exact (lowGeometry118C hn hθ).2

noncomputable def lowTIParameters119 : Parameters where
  wlo := (326676107/1000000000)
  whi := (344409047/500000000)
  clo := (20115947/50000000)
  chi := (579139237/1000000000)
  wE := (20096609/31250000)
  wS := (9/25)
  cE := (290226413/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (129874744453/200000000000)
  cLam := (585172563811/1000000000000)
  plane := (1/1)
  wRadius := (59531627/500000000)
  cRadius := (32342581/500000000)

theorem lowTIParameters119_valid : Valid lowTIParameters119 := by
  constructor
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters119,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters119,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]
  · norm_num [lowTIParameters119]

theorem lowTISupply119 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters119 (1039/2000) (13/25) := by
  refine ⟨lowTIParameters119_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters119]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters119]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry119W hn hθ).1 (by norm_num [lowTIParameters119])
      (by norm_num [lowTIParameters119]) (by norm_num [lowTIParameters119])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry119C hn hθ).1 (by norm_num [lowTIParameters119])
      (by norm_num [lowTIParameters119]) (by norm_num [lowTIParameters119])
  · intro θ hθ
    exact (lowGeometry119W hn hθ).2
  · intro θ hθ
    exact (lowGeometry119C hn hθ).2

noncomputable def lowTIParameters120 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (11911057/100000000)
  cRadius := (64715119/1000000000)

theorem lowTIParameters120_valid : Valid lowTIParameters120 := by
  constructor
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters120,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters120,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]
  · norm_num [lowTIParameters120]

theorem lowTISupply120 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters120 (13/25) (1041/2000) := by
  refine ⟨lowTIParameters120_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters120]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters120]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry120W hn hθ).1 (by norm_num [lowTIParameters120])
      (by norm_num [lowTIParameters120]) (by norm_num [lowTIParameters120])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry120C hn hθ).1 (by norm_num [lowTIParameters120])
      (by norm_num [lowTIParameters120]) (by norm_num [lowTIParameters120])
  · intro θ hθ
    exact (lowGeometry120W hn hθ).2
  · intro θ hθ
    exact (lowGeometry120C hn hθ).2

noncomputable def lowTIParameters121 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (119157819/1000000000)
  cRadius := (64745043/1000000000)

theorem lowTIParameters121_valid : Valid lowTIParameters121 := by
  constructor
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters121,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters121,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]
  · norm_num [lowTIParameters121]

theorem lowTISupply121 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters121 (1041/2000) (521/1000) := by
  refine ⟨lowTIParameters121_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters121]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters121]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry121W hn hθ).1 (by norm_num [lowTIParameters121])
      (by norm_num [lowTIParameters121]) (by norm_num [lowTIParameters121])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry121C hn hθ).1 (by norm_num [lowTIParameters121])
      (by norm_num [lowTIParameters121]) (by norm_num [lowTIParameters121])
  · intro θ hθ
    exact (lowGeometry121W hn hθ).2
  · intro θ hθ
    exact (lowGeometry121C hn hθ).2

noncomputable def lowTIParameters122 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (23841/200000)
  cRadius := (12954987/200000000)

theorem lowTIParameters122_valid : Valid lowTIParameters122 := by
  constructor
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters122,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters122,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]
  · norm_num [lowTIParameters122]

theorem lowTISupply122 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters122 (521/1000) (1043/2000) := by
  refine ⟨lowTIParameters122_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters122]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters122]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry122W hn hθ).1 (by norm_num [lowTIParameters122])
      (by norm_num [lowTIParameters122]) (by norm_num [lowTIParameters122])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry122C hn hθ).1 (by norm_num [lowTIParameters122])
      (by norm_num [lowTIParameters122]) (by norm_num [lowTIParameters122])
  · intro θ hθ
    exact (lowGeometry122W hn hθ).2
  · intro θ hθ
    exact (lowGeometry122C hn hθ).2

noncomputable def lowTIParameters123 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (23850423/200000000)
  cRadius := (12960959/200000000)

theorem lowTIParameters123_valid : Valid lowTIParameters123 := by
  constructor
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters123,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters123,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]
  · norm_num [lowTIParameters123]

theorem lowTISupply123 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters123 (1043/2000) (261/500) := by
  refine ⟨lowTIParameters123_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters123]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters123]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry123W hn hθ).1 (by norm_num [lowTIParameters123])
      (by norm_num [lowTIParameters123]) (by norm_num [lowTIParameters123])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry123C hn hθ).1 (by norm_num [lowTIParameters123])
      (by norm_num [lowTIParameters123]) (by norm_num [lowTIParameters123])
  · intro θ hθ
    exact (lowGeometry123W hn hθ).2
  · intro θ hθ
    exact (lowGeometry123C hn hθ).2

noncomputable def lowTIParameters124 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (59649581/500000000)
  cRadius := (32417311/500000000)

theorem lowTIParameters124_valid : Valid lowTIParameters124 := by
  constructor
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters124,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters124,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]
  · norm_num [lowTIParameters124]

theorem lowTISupply124 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters124 (261/500) (209/400) := by
  refine ⟨lowTIParameters124_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters124]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters124]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry124W hn hθ).1 (by norm_num [lowTIParameters124])
      (by norm_num [lowTIParameters124]) (by norm_num [lowTIParameters124])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry124C hn hθ).1 (by norm_num [lowTIParameters124])
      (by norm_num [lowTIParameters124]) (by norm_num [lowTIParameters124])
  · intro θ hθ
    exact (lowGeometry124W hn hθ).2
  · intro θ hθ
    exact (lowGeometry124C hn hθ).2

noncomputable def lowTIParameters125 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (119346141/1000000000)
  cRadius := (32432209/500000000)

theorem lowTIParameters125_valid : Valid lowTIParameters125 := by
  constructor
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters125,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters125,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]
  · norm_num [lowTIParameters125]

theorem lowTISupply125 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters125 (209/400) (523/1000) := by
  refine ⟨lowTIParameters125_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters125]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters125]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry125W hn hθ).1 (by norm_num [lowTIParameters125])
      (by norm_num [lowTIParameters125]) (by norm_num [lowTIParameters125])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry125C hn hθ).1 (by norm_num [lowTIParameters125])
      (by norm_num [lowTIParameters125]) (by norm_num [lowTIParameters125])
  · intro θ hθ
    exact (lowGeometry125W hn hθ).2
  · intro θ hθ
    exact (lowGeometry125C hn hθ).2

noncomputable def lowTIParameters126 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (59696527/500000000)
  cRadius := (64894181/1000000000)

theorem lowTIParameters126_valid : Valid lowTIParameters126 := by
  constructor
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters126,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters126,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]
  · norm_num [lowTIParameters126]

theorem lowTISupply126 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters126 (523/1000) (1047/2000) := by
  refine ⟨lowTIParameters126_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters126]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters126]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry126W hn hθ).1 (by norm_num [lowTIParameters126])
      (by norm_num [lowTIParameters126]) (by norm_num [lowTIParameters126])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry126C hn hθ).1 (by norm_num [lowTIParameters126])
      (by norm_num [lowTIParameters126]) (by norm_num [lowTIParameters126])
  · intro θ hθ
    exact (lowGeometry126W hn hθ).2
  · intro θ hθ
    exact (lowGeometry126C hn hθ).2

noncomputable def lowTIParameters127 : Parameters where
  wlo := (316744807/1000000000)
  whi := (339644381/500000000)
  clo := (392395949/1000000000)
  chi := (284607923/500000000)
  wE := (637130693/1000000000)
  wS := (9/25)
  cE := (115067499/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (643542133483/1000000000000)
  cLam := (580119968077/1000000000000)
  plane := (1/1)
  wRadius := (119439899/1000000000)
  cRadius := (64923911/1000000000)

theorem lowTIParameters127_valid : Valid lowTIParameters127 := by
  constructor
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters127,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters127,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]
  · norm_num [lowTIParameters127]

theorem lowTISupply127 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters127 (1047/2000) (131/250) := by
  refine ⟨lowTIParameters127_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters127]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters127]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry127W hn hθ).1 (by norm_num [lowTIParameters127])
      (by norm_num [lowTIParameters127]) (by norm_num [lowTIParameters127])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry127C hn hθ).1 (by norm_num [lowTIParameters127])
      (by norm_num [lowTIParameters127]) (by norm_num [lowTIParameters127])
  · intro θ hθ
    exact (lowGeometry127W hn hθ).2
  · intro θ hθ
    exact (lowGeometry127C hn hθ).2

end BstLean.BlueprintLow
