import BstLean.Part291GeometryBatch3
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters96 : Parameters where
  wlo := (168328459/500000000)
  whi := (69827511/100000000)
  clo := (412270461/1000000000)
  chi := (11780559/20000000)
  wE := (162280923/250000000)
  wS := (9/25)
  cE := (146407379/250000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (81910032713/125000000000)
  cLam := (147571850049/250000000000)
  plane := (1/1)
  wRadius := (117956453/1000000000)
  cRadius := (31993631/500000000)

theorem lowTIParameters96_valid : Valid lowTIParameters96 := by
  constructor
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters96,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters96,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]
  · norm_num [lowTIParameters96]

theorem lowTISupply96 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters96 (127/250) (1017/2000) := by
  refine ⟨lowTIParameters96_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters96]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters96]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry96W hn hθ).1 (by norm_num [lowTIParameters96])
      (by norm_num [lowTIParameters96]) (by norm_num [lowTIParameters96])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry96C hn hθ).1 (by norm_num [lowTIParameters96])
      (by norm_num [lowTIParameters96]) (by norm_num [lowTIParameters96])
  · intro θ hθ
    exact (lowGeometry96W hn hθ).2
  · intro θ hθ
    exact (lowGeometry96C hn hθ).2

noncomputable def lowTIParameters97 : Parameters where
  wlo := (168328459/500000000)
  whi := (69827511/100000000)
  clo := (412270461/1000000000)
  chi := (11780559/20000000)
  wE := (162280923/250000000)
  wS := (9/25)
  cE := (146407379/250000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (81910032713/125000000000)
  cLam := (147571850049/250000000000)
  plane := (1/1)
  wRadius := (118005313/1000000000)
  cRadius := (1600449/25000000)

theorem lowTIParameters97_valid : Valid lowTIParameters97 := by
  constructor
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters97,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters97,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]
  · norm_num [lowTIParameters97]

theorem lowTISupply97 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters97 (1017/2000) (509/1000) := by
  refine ⟨lowTIParameters97_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters97]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters97]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry97W hn hθ).1 (by norm_num [lowTIParameters97])
      (by norm_num [lowTIParameters97]) (by norm_num [lowTIParameters97])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry97C hn hθ).1 (by norm_num [lowTIParameters97])
      (by norm_num [lowTIParameters97]) (by norm_num [lowTIParameters97])
  · intro θ hθ
    exact (lowGeometry97W hn hθ).2
  · intro θ hθ
    exact (lowGeometry97C hn hθ).2

noncomputable def lowTIParameters98 : Parameters where
  wlo := (168328459/500000000)
  whi := (69827511/100000000)
  clo := (412270461/1000000000)
  chi := (11780559/20000000)
  wE := (162280923/250000000)
  wS := (9/25)
  cE := (146407379/250000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (81910032713/125000000000)
  cLam := (147571850049/250000000000)
  plane := (1/1)
  wRadius := (59027053/500000000)
  cRadius := (32024313/500000000)

theorem lowTIParameters98_valid : Valid lowTIParameters98 := by
  constructor
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters98,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters98,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]
  · norm_num [lowTIParameters98]

theorem lowTISupply98 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters98 (509/1000) (1019/2000) := by
  refine ⟨lowTIParameters98_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters98]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters98]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry98W hn hθ).1 (by norm_num [lowTIParameters98])
      (by norm_num [lowTIParameters98]) (by norm_num [lowTIParameters98])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry98C hn hθ).1 (by norm_num [lowTIParameters98])
      (by norm_num [lowTIParameters98]) (by norm_num [lowTIParameters98])
  · intro θ hθ
    exact (lowGeometry98W hn hθ).2
  · intro θ hθ
    exact (lowGeometry98C hn hθ).2

noncomputable def lowTIParameters99 : Parameters where
  wlo := (168328459/500000000)
  whi := (69827511/100000000)
  clo := (412270461/1000000000)
  chi := (11780559/20000000)
  wE := (162280923/250000000)
  wS := (9/25)
  cE := (146407379/250000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (81910032713/125000000000)
  cLam := (147571850049/250000000000)
  plane := (1/1)
  wRadius := (7381427/62500000)
  cRadius := (64079259/1000000000)

theorem lowTIParameters99_valid : Valid lowTIParameters99 := by
  constructor
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters99,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters99,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]
  · norm_num [lowTIParameters99]

theorem lowTISupply99 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters99 (1019/2000) (51/100) := by
  refine ⟨lowTIParameters99_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters99]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters99]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry99W hn hθ).1 (by norm_num [lowTIParameters99])
      (by norm_num [lowTIParameters99]) (by norm_num [lowTIParameters99])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry99C hn hθ).1 (by norm_num [lowTIParameters99])
      (by norm_num [lowTIParameters99]) (by norm_num [lowTIParameters99])
  · intro θ hθ
    exact (lowGeometry99W hn hθ).2
  · intro θ hθ
    exact (lowGeometry99C hn hθ).2

noncomputable def lowTIParameters100 : Parameters where
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
  wRadius := (118151491/1000000000)
  cRadius := (3205493/50000000)

theorem lowTIParameters100_valid : Valid lowTIParameters100 := by
  constructor
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters100,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters100,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]
  · norm_num [lowTIParameters100]

theorem lowTISupply100 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters100 (51/100) (1021/2000) := by
  refine ⟨lowTIParameters100_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters100]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters100]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry100W hn hθ).1 (by norm_num [lowTIParameters100])
      (by norm_num [lowTIParameters100]) (by norm_num [lowTIParameters100])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry100C hn hθ).1 (by norm_num [lowTIParameters100])
      (by norm_num [lowTIParameters100]) (by norm_num [lowTIParameters100])
  · intro θ hθ
    exact (lowGeometry100W hn hθ).2
  · intro θ hθ
    exact (lowGeometry100C hn hθ).2

noncomputable def lowTIParameters101 : Parameters where
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
  wRadius := (59100041/500000000)
  cRadius := (64140429/1000000000)

theorem lowTIParameters101_valid : Valid lowTIParameters101 := by
  constructor
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters101,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters101,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]
  · norm_num [lowTIParameters101]

theorem lowTISupply101 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters101 (1021/2000) (511/1000) := by
  refine ⟨lowTIParameters101_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters101]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters101]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry101W hn hθ).1 (by norm_num [lowTIParameters101])
      (by norm_num [lowTIParameters101]) (by norm_num [lowTIParameters101])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry101C hn hθ).1 (by norm_num [lowTIParameters101])
      (by norm_num [lowTIParameters101]) (by norm_num [lowTIParameters101])
  · intro θ hθ
    exact (lowGeometry101W hn hθ).2
  · intro θ hθ
    exact (lowGeometry101C hn hθ).2

noncomputable def lowTIParameters102 : Parameters where
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
  wRadius := (118248607/1000000000)
  cRadius := (32085483/500000000)

theorem lowTIParameters102_valid : Valid lowTIParameters102 := by
  constructor
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters102,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters102,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]
  · norm_num [lowTIParameters102]

theorem lowTISupply102 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters102 (511/1000) (1023/2000) := by
  refine ⟨lowTIParameters102_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters102]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters102]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry102W hn hθ).1 (by norm_num [lowTIParameters102])
      (by norm_num [lowTIParameters102]) (by norm_num [lowTIParameters102])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry102C hn hθ).1 (by norm_num [lowTIParameters102])
      (by norm_num [lowTIParameters102]) (by norm_num [lowTIParameters102])
  · intro θ hθ
    exact (lowGeometry102W hn hθ).2
  · intro θ hθ
    exact (lowGeometry102C hn hθ).2

noncomputable def lowTIParameters103 : Parameters where
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
  wRadius := (23659413/200000000)
  cRadius := (64201471/1000000000)

theorem lowTIParameters103_valid : Valid lowTIParameters103 := by
  constructor
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters103,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters103,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]
  · norm_num [lowTIParameters103]

theorem lowTISupply103 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters103 (1023/2000) (64/125) := by
  refine ⟨lowTIParameters103_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters103]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters103]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry103W hn hθ).1 (by norm_num [lowTIParameters103])
      (by norm_num [lowTIParameters103]) (by norm_num [lowTIParameters103])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry103C hn hθ).1 (by norm_num [lowTIParameters103])
      (by norm_num [lowTIParameters103]) (by norm_num [lowTIParameters103])
  · intro θ hθ
    exact (lowGeometry103W hn hθ).2
  · intro θ hθ
    exact (lowGeometry103C hn hθ).2

noncomputable def lowTIParameters104 : Parameters where
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
  wRadius := (23669091/200000000)
  cRadius := (64231943/1000000000)

theorem lowTIParameters104_valid : Valid lowTIParameters104 := by
  constructor
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters104,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters104,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]
  · norm_num [lowTIParameters104]

theorem lowTISupply104 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters104 (64/125) (41/80) := by
  refine ⟨lowTIParameters104_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters104]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters104]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry104W hn hθ).1 (by norm_num [lowTIParameters104])
      (by norm_num [lowTIParameters104]) (by norm_num [lowTIParameters104])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry104C hn hθ).1 (by norm_num [lowTIParameters104])
      (by norm_num [lowTIParameters104]) (by norm_num [lowTIParameters104])
  · intro θ hθ
    exact (lowGeometry104W hn hθ).2
  · intro θ hθ
    exact (lowGeometry104C hn hθ).2

noncomputable def lowTIParameters105 : Parameters where
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
  wRadius := (59196889/500000000)
  cRadius := (64262383/1000000000)

theorem lowTIParameters105_valid : Valid lowTIParameters105 := by
  constructor
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters105,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters105,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]
  · norm_num [lowTIParameters105]

theorem lowTISupply105 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters105 (41/80) (513/1000) := by
  refine ⟨lowTIParameters105_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters105]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters105]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry105W hn hθ).1 (by norm_num [lowTIParameters105])
      (by norm_num [lowTIParameters105]) (by norm_num [lowTIParameters105])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry105C hn hθ).1 (by norm_num [lowTIParameters105])
      (by norm_num [lowTIParameters105]) (by norm_num [lowTIParameters105])
  · intro θ hθ
    exact (lowGeometry105W hn hθ).2
  · intro θ hθ
    exact (lowGeometry105C hn hθ).2

noncomputable def lowTIParameters106 : Parameters where
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
  wRadius := (59221017/500000000)
  cRadius := (64292791/1000000000)

theorem lowTIParameters106_valid : Valid lowTIParameters106 := by
  constructor
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters106,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters106,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]
  · norm_num [lowTIParameters106]

theorem lowTISupply106 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters106 (513/1000) (1027/2000) := by
  refine ⟨lowTIParameters106_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters106]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters106]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry106W hn hθ).1 (by norm_num [lowTIParameters106])
      (by norm_num [lowTIParameters106]) (by norm_num [lowTIParameters106])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry106C hn hθ).1 (by norm_num [lowTIParameters106])
      (by norm_num [lowTIParameters106]) (by norm_num [lowTIParameters106])
  · intro θ hθ
    exact (lowGeometry106W hn hθ).2
  · intro θ hθ
    exact (lowGeometry106C hn hθ).2

noncomputable def lowTIParameters107 : Parameters where
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
  wRadius := (118490223/1000000000)
  cRadius := (64323167/1000000000)

theorem lowTIParameters107_valid : Valid lowTIParameters107 := by
  constructor
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters107,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters107,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]
  · norm_num [lowTIParameters107]

theorem lowTISupply107 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters107 (1027/2000) (257/500) := by
  refine ⟨lowTIParameters107_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters107]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters107]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry107W hn hθ).1 (by norm_num [lowTIParameters107])
      (by norm_num [lowTIParameters107]) (by norm_num [lowTIParameters107])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry107C hn hθ).1 (by norm_num [lowTIParameters107])
      (by norm_num [lowTIParameters107]) (by norm_num [lowTIParameters107])
  · intro θ hθ
    exact (lowGeometry107W hn hθ).2
  · intro θ hθ
    exact (lowGeometry107C hn hθ).2

noncomputable def lowTIParameters108 : Parameters where
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
  wRadius := (23707669/200000000)
  cRadius := (64353511/1000000000)

theorem lowTIParameters108_valid : Valid lowTIParameters108 := by
  constructor
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters108,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters108,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]
  · norm_num [lowTIParameters108]

theorem lowTISupply108 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters108 (257/500) (1029/2000) := by
  refine ⟨lowTIParameters108_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters108]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters108]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry108W hn hθ).1 (by norm_num [lowTIParameters108])
      (by norm_num [lowTIParameters108]) (by norm_num [lowTIParameters108])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry108C hn hθ).1 (by norm_num [lowTIParameters108])
      (by norm_num [lowTIParameters108]) (by norm_num [lowTIParameters108])
  · intro θ hθ
    exact (lowGeometry108W hn hθ).2
  · intro θ hθ
    exact (lowGeometry108C hn hθ).2

noncomputable def lowTIParameters109 : Parameters where
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
  wRadius := (148233/1250000)
  cRadius := (32191911/500000000)

theorem lowTIParameters109_valid : Valid lowTIParameters109 := by
  constructor
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters109,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters109,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]
  · norm_num [lowTIParameters109]

theorem lowTISupply109 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters109 (1029/2000) (103/200) := by
  refine ⟨lowTIParameters109_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters109]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters109]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry109W hn hθ).1 (by norm_num [lowTIParameters109])
      (by norm_num [lowTIParameters109]) (by norm_num [lowTIParameters109])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry109C hn hθ).1 (by norm_num [lowTIParameters109])
      (by norm_num [lowTIParameters109]) (by norm_num [lowTIParameters109])
  · intro θ hθ
    exact (lowGeometry109W hn hθ).2
  · intro θ hθ
    exact (lowGeometry109C hn hθ).2

noncomputable def lowTIParameters110 : Parameters where
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
  wRadius := (29658597/250000000)
  cRadius := (64414101/1000000000)

theorem lowTIParameters110_valid : Valid lowTIParameters110 := by
  constructor
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters110,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters110,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]
  · norm_num [lowTIParameters110]

theorem lowTISupply110 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters110 (103/200) (1031/2000) := by
  refine ⟨lowTIParameters110_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters110]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters110]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry110W hn hθ).1 (by norm_num [lowTIParameters110])
      (by norm_num [lowTIParameters110]) (by norm_num [lowTIParameters110])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry110C hn hθ).1 (by norm_num [lowTIParameters110])
      (by norm_num [lowTIParameters110]) (by norm_num [lowTIParameters110])
  · intro θ hθ
    exact (lowGeometry110W hn hθ).2
  · intro θ hθ
    exact (lowGeometry110C hn hθ).2

noncomputable def lowTIParameters111 : Parameters where
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
  wRadius := (29670577/250000000)
  cRadius := (16111087/250000000)

theorem lowTIParameters111_valid : Valid lowTIParameters111 := by
  constructor
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · have h : √((((20096609/31250000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (29565595653/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters111,ta_lam] at h ⊢
    linarith
  · have h : √((((290226413/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (194946150811/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters111,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]
  · norm_num [lowTIParameters111]

theorem lowTISupply111 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters111 (1031/2000) (129/250) := by
  refine ⟨lowTIParameters111_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum100W hn using 1 <;> norm_num [lowTIParameters111]
  · convert lowUniformNum100C hn using 1 <;> norm_num [lowTIParameters111]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry111W hn hθ).1 (by norm_num [lowTIParameters111])
      (by norm_num [lowTIParameters111]) (by norm_num [lowTIParameters111])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry111C hn hθ).1 (by norm_num [lowTIParameters111])
      (by norm_num [lowTIParameters111]) (by norm_num [lowTIParameters111])
  · intro θ hθ
    exact (lowGeometry111W hn hθ).2
  · intro θ hθ
    exact (lowGeometry111C hn hθ).2

end BstLean.BlueprintLow
