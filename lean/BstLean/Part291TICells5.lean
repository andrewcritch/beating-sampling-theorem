import BstLean.Part291GeometryBatch2
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters80 : Parameters where
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
  wRadius := (29291393/250000000)
  cRadius := (1587293/25000000)

theorem lowTIParameters80_valid : Valid lowTIParameters80 := by
  constructor
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters80,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters80,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]
  · norm_num [lowTIParameters80]

theorem lowTISupply80 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters80 (1/2) (1001/2000) := by
  refine ⟨lowTIParameters80_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters80]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters80]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry80W hn hθ).1 (by norm_num [lowTIParameters80])
      (by norm_num [lowTIParameters80]) (by norm_num [lowTIParameters80])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry80C hn hθ).1 (by norm_num [lowTIParameters80])
      (by norm_num [lowTIParameters80]) (by norm_num [lowTIParameters80])
  · intro θ hθ
    exact (lowGeometry80W hn hθ).2
  · intro θ hθ
    exact (lowGeometry80C hn hθ).2

noncomputable def lowTIParameters81 : Parameters where
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
  wRadius := (23443101/200000000)
  cRadius := (15880733/250000000)

theorem lowTIParameters81_valid : Valid lowTIParameters81 := by
  constructor
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters81,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters81,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]
  · norm_num [lowTIParameters81]

theorem lowTISupply81 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters81 (1001/2000) (501/1000) := by
  refine ⟨lowTIParameters81_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters81]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters81]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry81W hn hθ).1 (by norm_num [lowTIParameters81])
      (by norm_num [lowTIParameters81]) (by norm_num [lowTIParameters81])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry81C hn hθ).1 (by norm_num [lowTIParameters81])
      (by norm_num [lowTIParameters81]) (by norm_num [lowTIParameters81])
  · intro θ hθ
    exact (lowGeometry81W hn hθ).2
  · intro θ hθ
    exact (lowGeometry81C hn hθ).2

noncomputable def lowTIParameters82 : Parameters where
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
  wRadius := (117265371/1000000000)
  cRadius := (63554113/1000000000)

theorem lowTIParameters82_valid : Valid lowTIParameters82 := by
  constructor
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters82,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters82,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]
  · norm_num [lowTIParameters82]

theorem lowTISupply82 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters82 (501/1000) (1003/2000) := by
  refine ⟨lowTIParameters82_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters82]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters82]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry82W hn hθ).1 (by norm_num [lowTIParameters82])
      (by norm_num [lowTIParameters82]) (by norm_num [lowTIParameters82])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry82C hn hθ).1 (by norm_num [lowTIParameters82])
      (by norm_num [lowTIParameters82]) (by norm_num [lowTIParameters82])
  · intro θ hθ
    exact (lowGeometry82W hn hθ).2
  · intro θ hθ
    exact (lowGeometry82C hn hθ).2

noncomputable def lowTIParameters83 : Parameters where
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
  wRadius := (11731517/100000000)
  cRadius := (31792631/500000000)

theorem lowTIParameters83_valid : Valid lowTIParameters83 := by
  constructor
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters83,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters83,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]
  · norm_num [lowTIParameters83]

theorem lowTISupply83 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters83 (1003/2000) (251/500) := by
  refine ⟨lowTIParameters83_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters83]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters83]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry83W hn hθ).1 (by norm_num [lowTIParameters83])
      (by norm_num [lowTIParameters83]) (by norm_num [lowTIParameters83])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry83C hn hθ).1 (by norm_num [lowTIParameters83])
      (by norm_num [lowTIParameters83]) (by norm_num [lowTIParameters83])
  · intro θ hθ
    exact (lowGeometry83W hn hθ).2
  · intro θ hθ
    exact (lowGeometry83C hn hθ).2

noncomputable def lowTIParameters84 : Parameters where
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
  wRadius := (58682451/500000000)
  cRadius := (31808189/500000000)

theorem lowTIParameters84_valid : Valid lowTIParameters84 := by
  constructor
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters84,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters84,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]
  · norm_num [lowTIParameters84]

theorem lowTISupply84 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters84 (251/500) (201/400) := by
  refine ⟨lowTIParameters84_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters84]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters84]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry84W hn hθ).1 (by norm_num [lowTIParameters84])
      (by norm_num [lowTIParameters84]) (by norm_num [lowTIParameters84])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry84C hn hθ).1 (by norm_num [lowTIParameters84])
      (by norm_num [lowTIParameters84]) (by norm_num [lowTIParameters84])
  · intro θ hθ
    exact (lowGeometry84W hn hθ).2
  · intro θ hθ
    exact (lowGeometry84C hn hθ).2

noncomputable def lowTIParameters85 : Parameters where
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
  wRadius := (117414567/1000000000)
  cRadius := (31823731/500000000)

theorem lowTIParameters85_valid : Valid lowTIParameters85 := by
  constructor
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters85,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters85,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]
  · norm_num [lowTIParameters85]

theorem lowTISupply85 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters85 (201/400) (503/1000) := by
  refine ⟨lowTIParameters85_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters85]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters85]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry85W hn hθ).1 (by norm_num [lowTIParameters85])
      (by norm_num [lowTIParameters85]) (by norm_num [lowTIParameters85])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry85C hn hθ).1 (by norm_num [lowTIParameters85])
      (by norm_num [lowTIParameters85]) (by norm_num [lowTIParameters85])
  · intro θ hθ
    exact (lowGeometry85W hn hθ).2
  · intro θ hθ
    exact (lowGeometry85C hn hθ).2

noncomputable def lowTIParameters86 : Parameters where
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
  wRadius := (29366041/250000000)
  cRadius := (31839257/500000000)

theorem lowTIParameters86_valid : Valid lowTIParameters86 := by
  constructor
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters86,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters86,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]
  · norm_num [lowTIParameters86]

theorem lowTISupply86 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters86 (503/1000) (1007/2000) := by
  refine ⟨lowTIParameters86_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters86]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters86]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry86W hn hθ).1 (by norm_num [lowTIParameters86])
      (by norm_num [lowTIParameters86]) (by norm_num [lowTIParameters86])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry86C hn hθ).1 (by norm_num [lowTIParameters86])
      (by norm_num [lowTIParameters86]) (by norm_num [lowTIParameters86])
  · intro θ hθ
    exact (lowGeometry86W hn hθ).2
  · intro θ hθ
    exact (lowGeometry86C hn hθ).2

noncomputable def lowTIParameters87 : Parameters where
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
  wRadius := (23502739/200000000)
  cRadius := (63709533/1000000000)

theorem lowTIParameters87_valid : Valid lowTIParameters87 := by
  constructor
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters87,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters87,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]
  · norm_num [lowTIParameters87]

theorem lowTISupply87 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters87 (1007/2000) (63/125) := by
  refine ⟨lowTIParameters87_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters87]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters87]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry87W hn hθ).1 (by norm_num [lowTIParameters87])
      (by norm_num [lowTIParameters87]) (by norm_num [lowTIParameters87])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry87C hn hθ).1 (by norm_num [lowTIParameters87])
      (by norm_num [lowTIParameters87]) (by norm_num [lowTIParameters87])
  · intro θ hθ
    exact (lowGeometry87W hn hθ).2
  · intro θ hθ
    exact (lowGeometry87C hn hθ).2

noncomputable def lowTIParameters88 : Parameters where
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
  wRadius := (117563159/1000000000)
  cRadius := (63740521/1000000000)

theorem lowTIParameters88_valid : Valid lowTIParameters88 := by
  constructor
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters88,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters88,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]
  · norm_num [lowTIParameters88]

theorem lowTISupply88 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters88 (63/125) (1009/2000) := by
  refine ⟨lowTIParameters88_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters88]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters88]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry88W hn hθ).1 (by norm_num [lowTIParameters88])
      (by norm_num [lowTIParameters88]) (by norm_num [lowTIParameters88])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry88C hn hθ).1 (by norm_num [lowTIParameters88])
      (by norm_num [lowTIParameters88]) (by norm_num [lowTIParameters88])
  · intro θ hθ
    exact (lowGeometry88W hn hθ).2
  · intro θ hθ
    exact (lowGeometry88C hn hθ).2

noncomputable def lowTIParameters89 : Parameters where
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
  wRadius := (23522511/200000000)
  cRadius := (15942869/250000000)

theorem lowTIParameters89_valid : Valid lowTIParameters89 := by
  constructor
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters89,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters89,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]
  · norm_num [lowTIParameters89]

theorem lowTISupply89 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters89 (1009/2000) (101/200) := by
  refine ⟨lowTIParameters89_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters89]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters89]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry89W hn hθ).1 (by norm_num [lowTIParameters89])
      (by norm_num [lowTIParameters89]) (by norm_num [lowTIParameters89])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry89C hn hθ).1 (by norm_num [lowTIParameters89])
      (by norm_num [lowTIParameters89]) (by norm_num [lowTIParameters89])
  · intro θ hθ
    exact (lowGeometry89W hn hθ).2
  · intro θ hθ
    exact (lowGeometry89C hn hθ).2

noncomputable def lowTIParameters90 : Parameters where
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
  wRadius := (23532377/200000000)
  cRadius := (79753/1250000)

theorem lowTIParameters90_valid : Valid lowTIParameters90 := by
  constructor
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters90,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters90,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]
  · norm_num [lowTIParameters90]

theorem lowTISupply90 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters90 (101/200) (1011/2000) := by
  refine ⟨lowTIParameters90_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters90]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters90]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry90W hn hθ).1 (by norm_num [lowTIParameters90])
      (by norm_num [lowTIParameters90]) (by norm_num [lowTIParameters90])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry90C hn hθ).1 (by norm_num [lowTIParameters90])
      (by norm_num [lowTIParameters90]) (by norm_num [lowTIParameters90])
  · intro θ hθ
    exact (lowGeometry90W hn hθ).2
  · intro θ hθ
    exact (lowGeometry90C hn hθ).2

noncomputable def lowTIParameters91 : Parameters where
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
  wRadius := (117711147/1000000000)
  cRadius := (6383329/100000000)

theorem lowTIParameters91_valid : Valid lowTIParameters91 := by
  constructor
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters91,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters91,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]
  · norm_num [lowTIParameters91]

theorem lowTISupply91 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters91 (1011/2000) (253/500) := by
  refine ⟨lowTIParameters91_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters91]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters91]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry91W hn hθ).1 (by norm_num [lowTIParameters91])
      (by norm_num [lowTIParameters91]) (by norm_num [lowTIParameters91])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry91C hn hθ).1 (by norm_num [lowTIParameters91])
      (by norm_num [lowTIParameters91]) (by norm_num [lowTIParameters91])
  · intro θ hθ
    exact (lowGeometry91W hn hθ).2
  · intro θ hθ
    exact (lowGeometry91C hn hθ).2

noncomputable def lowTIParameters92 : Parameters where
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
  wRadius := (58880171/500000000)
  cRadius := (63864149/1000000000)

theorem lowTIParameters92_valid : Valid lowTIParameters92 := by
  constructor
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters92,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters92,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]
  · norm_num [lowTIParameters92]

theorem lowTISupply92 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters92 (253/500) (1013/2000) := by
  refine ⟨lowTIParameters92_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters92]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters92]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry92W hn hθ).1 (by norm_num [lowTIParameters92])
      (by norm_num [lowTIParameters92]) (by norm_num [lowTIParameters92])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry92C hn hθ).1 (by norm_num [lowTIParameters92])
      (by norm_num [lowTIParameters92]) (by norm_num [lowTIParameters92])
  · intro θ hθ
    exact (lowGeometry92W hn hθ).2
  · intro θ hθ
    exact (lowGeometry92C hn hθ).2

noncomputable def lowTIParameters93 : Parameters where
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
  wRadius := (117809471/1000000000)
  cRadius := (998359/15625000)

theorem lowTIParameters93_valid : Valid lowTIParameters93 := by
  constructor
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters93,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters93,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]
  · norm_num [lowTIParameters93]

theorem lowTISupply93 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters93 (1013/2000) (507/1000) := by
  refine ⟨lowTIParameters93_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters93]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters93]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry93W hn hθ).1 (by norm_num [lowTIParameters93])
      (by norm_num [lowTIParameters93]) (by norm_num [lowTIParameters93])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry93C hn hθ).1 (by norm_num [lowTIParameters93])
      (by norm_num [lowTIParameters93]) (by norm_num [lowTIParameters93])
  · intro θ hθ
    exact (lowGeometry93W hn hθ).2
  · intro θ hθ
    exact (lowGeometry93C hn hθ).2

noncomputable def lowTIParameters94 : Parameters where
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
  wRadius := (29464633/250000000)
  cRadius := (6392577/100000000)

theorem lowTIParameters94_valid : Valid lowTIParameters94 := by
  constructor
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters94,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters94,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]
  · norm_num [lowTIParameters94]

theorem lowTISupply94 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters94 (507/1000) (203/400) := by
  refine ⟨lowTIParameters94_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters94]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters94]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry94W hn hθ).1 (by norm_num [lowTIParameters94])
      (by norm_num [lowTIParameters94]) (by norm_num [lowTIParameters94])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry94C hn hθ).1 (by norm_num [lowTIParameters94])
      (by norm_num [lowTIParameters94]) (by norm_num [lowTIParameters94])
  · intro θ hθ
    exact (lowGeometry94W hn hθ).2
  · intro θ hθ
    exact (lowGeometry94C hn hθ).2

noncomputable def lowTIParameters95 : Parameters where
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
  wRadius := (58953763/500000000)
  cRadius := (15989133/250000000)

theorem lowTIParameters95_valid : Valid lowTIParameters95 := by
  constructor
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · have h : √((((162280923/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (18839801963/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters95,ta_lam] at h ⊢
    linarith
  · have h : √((((146407379/250000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (49368160549/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters95,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]
  · norm_num [lowTIParameters95]

theorem lowTISupply95 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters95 (203/400) (127/250) := by
  refine ⟨lowTIParameters95_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum80W hn using 1 <;> norm_num [lowTIParameters95]
  · convert lowUniformNum80C hn using 1 <;> norm_num [lowTIParameters95]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry95W hn hθ).1 (by norm_num [lowTIParameters95])
      (by norm_num [lowTIParameters95]) (by norm_num [lowTIParameters95])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry95C hn hθ).1 (by norm_num [lowTIParameters95])
      (by norm_num [lowTIParameters95]) (by norm_num [lowTIParameters95])
  · intro θ hθ
    exact (lowGeometry95W hn hθ).2
  · intro θ hθ
    exact (lowGeometry95C hn hθ).2

end BstLean.BlueprintLow
