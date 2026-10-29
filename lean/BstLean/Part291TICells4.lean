import BstLean.Part291GeometryBatch2
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters64 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (58178763/500000000)
  cRadius := (62987937/1000000000)

theorem lowTIParameters64_valid : Valid lowTIParameters64 := by
  constructor
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters64,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters64,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]
  · norm_num [lowTIParameters64]

theorem lowTISupply64 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters64 (123/250) (197/400) := by
  refine ⟨lowTIParameters64_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters64]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters64]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry64W hn hθ).1 (by norm_num [lowTIParameters64])
      (by norm_num [lowTIParameters64]) (by norm_num [lowTIParameters64])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry64C hn hθ).1 (by norm_num [lowTIParameters64])
      (by norm_num [lowTIParameters64]) (by norm_num [lowTIParameters64])
  · intro θ hθ
    exact (lowGeometry64W hn hθ).2
  · intro θ hθ
    exact (lowGeometry64C hn hθ).2

noncomputable def lowTIParameters65 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (29102133/250000000)
  cRadius := (12603933/200000000)

theorem lowTIParameters65_valid : Valid lowTIParameters65 := by
  constructor
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters65,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters65,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]
  · norm_num [lowTIParameters65]

theorem lowTISupply65 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters65 (197/400) (493/1000) := by
  refine ⟨lowTIParameters65_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters65]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters65]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry65W hn hθ).1 (by norm_num [lowTIParameters65])
      (by norm_num [lowTIParameters65]) (by norm_num [lowTIParameters65])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry65C hn hθ).1 (by norm_num [lowTIParameters65])
      (by norm_num [lowTIParameters65]) (by norm_num [lowTIParameters65])
  · intro θ hθ
    exact (lowGeometry65W hn hθ).2
  · intro θ hθ
    exact (lowGeometry65C hn hθ).2

noncomputable def lowTIParameters66 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (116459471/1000000000)
  cRadius := (63051361/1000000000)

theorem lowTIParameters66_valid : Valid lowTIParameters66 := by
  constructor
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters66,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters66,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]
  · norm_num [lowTIParameters66]

theorem lowTISupply66 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters66 (493/1000) (987/2000) := by
  refine ⟨lowTIParameters66_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters66]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters66]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry66W hn hθ).1 (by norm_num [lowTIParameters66])
      (by norm_num [lowTIParameters66]) (by norm_num [lowTIParameters66])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry66C hn hθ).1 (by norm_num [lowTIParameters66])
      (by norm_num [lowTIParameters66]) (by norm_num [lowTIParameters66])
  · intro θ hθ
    exact (lowGeometry66W hn hθ).2
  · intro θ hθ
    exact (lowGeometry66C hn hθ).2

noncomputable def lowTIParameters67 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (58255171/500000000)
  cRadius := (3942689/62500000)

theorem lowTIParameters67_valid : Valid lowTIParameters67 := by
  constructor
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters67,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters67,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]
  · norm_num [lowTIParameters67]

theorem lowTISupply67 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters67 (987/2000) (247/500) := by
  refine ⟨lowTIParameters67_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters67]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters67]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry67W hn hθ).1 (by norm_num [lowTIParameters67])
      (by norm_num [lowTIParameters67]) (by norm_num [lowTIParameters67])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry67C hn hθ).1 (by norm_num [lowTIParameters67])
      (by norm_num [lowTIParameters67]) (by norm_num [lowTIParameters67])
  · intro θ hθ
    exact (lowGeometry67W hn hθ).2
  · intro θ hθ
    exact (lowGeometry67C hn hθ).2

noncomputable def lowTIParameters68 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (116561147/1000000000)
  cRadius := (12622931/200000000)

theorem lowTIParameters68_valid : Valid lowTIParameters68 := by
  constructor
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters68,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters68,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]
  · norm_num [lowTIParameters68]

theorem lowTISupply68 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters68 (247/500) (989/2000) := by
  refine ⟨lowTIParameters68_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters68]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters68]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry68W hn hθ).1 (by norm_num [lowTIParameters68])
      (by norm_num [lowTIParameters68]) (by norm_num [lowTIParameters68])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry68C hn hθ).1 (by norm_num [lowTIParameters68])
      (by norm_num [lowTIParameters68]) (by norm_num [lowTIParameters68])
  · intro θ hθ
    exact (lowGeometry68W hn hθ).2
  · intro θ hθ
    exact (lowGeometry68C hn hθ).2

noncomputable def lowTIParameters69 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (23322377/200000000)
  cRadius := (12629251/200000000)

theorem lowTIParameters69_valid : Valid lowTIParameters69 := by
  constructor
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters69,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters69,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]
  · norm_num [lowTIParameters69]

theorem lowTISupply69 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters69 (989/2000) (99/200) := by
  refine ⟨lowTIParameters69_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters69]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters69]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry69W hn hθ).1 (by norm_num [lowTIParameters69])
      (by norm_num [lowTIParameters69]) (by norm_num [lowTIParameters69])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry69C hn hθ).1 (by norm_num [lowTIParameters69])
      (by norm_num [lowTIParameters69]) (by norm_num [lowTIParameters69])
  · intro θ hθ
    exact (lowGeometry69W hn hθ).2
  · intro θ hθ
    exact (lowGeometry69C hn hθ).2

noncomputable def lowTIParameters70 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (23332511/200000000)
  cRadius := (63177821/1000000000)

theorem lowTIParameters70_valid : Valid lowTIParameters70 := by
  constructor
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters70,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters70,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]
  · norm_num [lowTIParameters70]

theorem lowTISupply70 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters70 (99/200) (991/2000) := by
  refine ⟨lowTIParameters70_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters70]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters70]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry70W hn hθ).1 (by norm_num [lowTIParameters70])
      (by norm_num [lowTIParameters70]) (by norm_num [lowTIParameters70])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry70C hn hθ).1 (by norm_num [lowTIParameters70])
      (by norm_num [lowTIParameters70]) (by norm_num [lowTIParameters70])
  · intro θ hθ
    exact (lowGeometry70W hn hθ).2
  · intro θ hθ
    exact (lowGeometry70C hn hθ).2

noncomputable def lowTIParameters71 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (116713159/1000000000)
  cRadius := (15802339/250000000)

theorem lowTIParameters71_valid : Valid lowTIParameters71 := by
  constructor
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters71,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters71,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]
  · norm_num [lowTIParameters71]

theorem lowTISupply71 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters71 (991/2000) (62/125) := by
  refine ⟨lowTIParameters71_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters71]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters71]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry71W hn hθ).1 (by norm_num [lowTIParameters71])
      (by norm_num [lowTIParameters71]) (by norm_num [lowTIParameters71])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry71C hn hθ).1 (by norm_num [lowTIParameters71])
      (by norm_num [lowTIParameters71]) (by norm_num [lowTIParameters71])
  · intro θ hθ
    exact (lowGeometry71W hn hθ).2
  · intro θ hθ
    exact (lowGeometry71C hn hθ).2

noncomputable def lowTIParameters72 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (23352739/200000000)
  cRadius := (63240859/1000000000)

theorem lowTIParameters72_valid : Valid lowTIParameters72 := by
  constructor
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters72,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters72,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]
  · norm_num [lowTIParameters72]

theorem lowTISupply72 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters72 (62/125) (993/2000) := by
  refine ⟨lowTIParameters72_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters72]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters72]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry72W hn hθ).1 (by norm_num [lowTIParameters72])
      (by norm_num [lowTIParameters72]) (by norm_num [lowTIParameters72])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry72C hn hθ).1 (by norm_num [lowTIParameters72])
      (by norm_num [lowTIParameters72]) (by norm_num [lowTIParameters72])
  · intro θ hθ
    exact (lowGeometry72W hn hθ).2
  · intro θ hθ
    exact (lowGeometry72C hn hθ).2

noncomputable def lowTIParameters73 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (29203541/250000000)
  cRadius := (63272329/1000000000)

theorem lowTIParameters73_valid : Valid lowTIParameters73 := by
  constructor
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters73,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters73,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]
  · norm_num [lowTIParameters73]

theorem lowTISupply73 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters73 (993/2000) (497/1000) := by
  refine ⟨lowTIParameters73_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters73]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters73]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry73W hn hθ).1 (by norm_num [lowTIParameters73])
      (by norm_num [lowTIParameters73]) (by norm_num [lowTIParameters73])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry73C hn hθ).1 (by norm_num [lowTIParameters73])
      (by norm_num [lowTIParameters73]) (by norm_num [lowTIParameters73])
  · intro θ hθ
    exact (lowGeometry73W hn hθ).2
  · intro θ hθ
    exact (lowGeometry73C hn hθ).2

noncomputable def lowTIParameters74 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (116864567/1000000000)
  cRadius := (63303767/1000000000)

theorem lowTIParameters74_valid : Valid lowTIParameters74 := by
  constructor
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters74,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters74,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]
  · norm_num [lowTIParameters74]

theorem lowTISupply74 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters74 (497/1000) (199/400) := by
  refine ⟨lowTIParameters74_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters74]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters74]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry74W hn hθ).1 (by norm_num [lowTIParameters74])
      (by norm_num [lowTIParameters74]) (by norm_num [lowTIParameters74])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry74C hn hθ).1 (by norm_num [lowTIParameters74])
      (by norm_num [lowTIParameters74]) (by norm_num [lowTIParameters74])
  · intro θ hθ
    exact (lowGeometry74W hn hθ).2
  · intro θ hθ
    exact (lowGeometry74C hn hθ).2

noncomputable def lowTIParameters75 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (58457451/500000000)
  cRadius := (63335173/1000000000)

theorem lowTIParameters75_valid : Valid lowTIParameters75 := by
  constructor
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters75,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters75,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]
  · norm_num [lowTIParameters75]

theorem lowTISupply75 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters75 (199/400) (249/500) := by
  refine ⟨lowTIParameters75_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters75]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters75]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry75W hn hθ).1 (by norm_num [lowTIParameters75])
      (by norm_num [lowTIParameters75]) (by norm_num [lowTIParameters75])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry75C hn hθ).1 (by norm_num [lowTIParameters75])
      (by norm_num [lowTIParameters75]) (by norm_num [lowTIParameters75])
  · intro θ hθ
    exact (lowGeometry75W hn hθ).2
  · intro θ hθ
    exact (lowGeometry75C hn hθ).2

noncomputable def lowTIParameters76 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (11696517/100000000)
  cRadius := (63366547/1000000000)

theorem lowTIParameters76_valid : Valid lowTIParameters76 := by
  constructor
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters76,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters76,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]
  · norm_num [lowTIParameters76]

theorem lowTISupply76 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters76 (249/500) (997/2000) := by
  refine ⟨lowTIParameters76_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters76]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters76]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry76W hn hθ).1 (by norm_num [lowTIParameters76])
      (by norm_num [lowTIParameters76]) (by norm_num [lowTIParameters76])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry76C hn hθ).1 (by norm_num [lowTIParameters76])
      (by norm_num [lowTIParameters76]) (by norm_num [lowTIParameters76])
  · intro θ hθ
    exact (lowGeometry76W hn hθ).2
  · intro θ hθ
    exact (lowGeometry76C hn hθ).2

noncomputable def lowTIParameters77 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (117015371/1000000000)
  cRadius := (123824/1953125)

theorem lowTIParameters77_valid : Valid lowTIParameters77 := by
  constructor
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters77,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters77,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]
  · norm_num [lowTIParameters77]

theorem lowTISupply77 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters77 (997/2000) (499/1000) := by
  refine ⟨lowTIParameters77_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters77]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters77]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry77W hn hθ).1 (by norm_num [lowTIParameters77])
      (by norm_num [lowTIParameters77]) (by norm_num [lowTIParameters77])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry77C hn hθ).1 (by norm_num [lowTIParameters77])
      (by norm_num [lowTIParameters77]) (by norm_num [lowTIParameters77])
  · intro θ hθ
    exact (lowGeometry77W hn hθ).2
  · intro θ hθ
    exact (lowGeometry77C hn hθ).2

noncomputable def lowTIParameters78 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (23413101/200000000)
  cRadius := (63429197/1000000000)

theorem lowTIParameters78_valid : Valid lowTIParameters78 := by
  constructor
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters78,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters78,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]
  · norm_num [lowTIParameters78]

theorem lowTISupply78 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters78 (499/1000) (999/2000) := by
  refine ⟨lowTIParameters78_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters78]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters78]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry78W hn hθ).1 (by norm_num [lowTIParameters78])
      (by norm_num [lowTIParameters78]) (by norm_num [lowTIParameters78])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry78C hn hθ).1 (by norm_num [lowTIParameters78])
      (by norm_num [lowTIParameters78]) (by norm_num [lowTIParameters78])
  · intro θ hθ
    exact (lowGeometry78W hn hθ).2
  · intro θ hθ
    exact (lowGeometry78C hn hθ).2

noncomputable def lowTIParameters79 : Parameters where
  wlo := (69337607/200000000)
  whi := (707659223/1000000000)
  clo := (26390681/62500000)
  chi := (598881659/1000000000)
  wE := (131045987/200000000)
  wS := (9/25)
  cE := (118173913/200000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (661264217883/1000000000000)
  cLam := (74433306163/125000000000)
  plane := (1/1)
  wRadius := (29278893/250000000)
  cRadius := (2538419/40000000)

theorem lowTIParameters79_valid : Valid lowTIParameters79 := by
  constructor
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · have h : √((((131045987/200000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (153649250383/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters79,ta_lam] at h ⊢
    linarith
  · have h : √((((118173913/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (50007916701/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters79,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]
  · norm_num [lowTIParameters79]

theorem lowTISupply79 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters79 (999/2000) (1/2) := by
  refine ⟨lowTIParameters79_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum60W hn using 1 <;> norm_num [lowTIParameters79]
  · convert lowUniformNum60C hn using 1 <;> norm_num [lowTIParameters79]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry79W hn hθ).1 (by norm_num [lowTIParameters79])
      (by norm_num [lowTIParameters79]) (by norm_num [lowTIParameters79])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry79C hn hθ).1 (by norm_num [lowTIParameters79])
      (by norm_num [lowTIParameters79]) (by norm_num [lowTIParameters79])
  · intro θ hθ
    exact (lowGeometry79W hn hθ).2
  · intro θ hθ
    exact (lowGeometry79C hn hθ).2

end BstLean.BlueprintLow
