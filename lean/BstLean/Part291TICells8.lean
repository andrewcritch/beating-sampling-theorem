import BstLean.Part291GeometryBatch4
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters128 : Parameters where
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
  wRadius := (119486677/1000000000)
  cRadius := (6495361/100000000)

theorem lowTIParameters128_valid : Valid lowTIParameters128 := by
  constructor
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters128,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters128,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]
  · norm_num [lowTIParameters128]

theorem lowTISupply128 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters128 (131/250) (1049/2000) := by
  refine ⟨lowTIParameters128_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters128]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters128]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry128W hn hθ).1 (by norm_num [lowTIParameters128])
      (by norm_num [lowTIParameters128]) (by norm_num [lowTIParameters128])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry128C hn hθ).1 (by norm_num [lowTIParameters128])
      (by norm_num [lowTIParameters128]) (by norm_num [lowTIParameters128])
  · intro θ hθ
    exact (lowGeometry128W hn hθ).2
  · intro θ hθ
    exact (lowGeometry128C hn hθ).2

noncomputable def lowTIParameters129 : Parameters where
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
  wRadius := (29883347/250000000)
  cRadius := (16245819/250000000)

theorem lowTIParameters129_valid : Valid lowTIParameters129 := by
  constructor
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters129,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters129,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]
  · norm_num [lowTIParameters129]

theorem lowTISupply129 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters129 (1049/2000) (21/40) := by
  refine ⟨lowTIParameters129_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters129]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters129]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry129W hn hθ).1 (by norm_num [lowTIParameters129])
      (by norm_num [lowTIParameters129]) (by norm_num [lowTIParameters129])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry129C hn hθ).1 (by norm_num [lowTIParameters129])
      (by norm_num [lowTIParameters129]) (by norm_num [lowTIParameters129])
  · intro θ hθ
    exact (lowGeometry129W hn hθ).2
  · intro θ hθ
    exact (lowGeometry129C hn hθ).2

noncomputable def lowTIParameters130 : Parameters where
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
  wRadius := (119580031/1000000000)
  cRadius := (6501291/100000000)

theorem lowTIParameters130_valid : Valid lowTIParameters130 := by
  constructor
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters130,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters130,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]
  · norm_num [lowTIParameters130]

theorem lowTISupply130 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters130 (21/40) (1051/2000) := by
  refine ⟨lowTIParameters130_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters130]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters130]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry130W hn hθ).1 (by norm_num [lowTIParameters130])
      (by norm_num [lowTIParameters130]) (by norm_num [lowTIParameters130])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry130C hn hθ).1 (by norm_num [lowTIParameters130])
      (by norm_num [lowTIParameters130]) (by norm_num [lowTIParameters130])
  · intro θ hθ
    exact (lowGeometry130W hn hθ).2
  · intro θ hθ
    exact (lowGeometry130C hn hθ).2

noncomputable def lowTIParameters131 : Parameters where
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
  wRadius := (119626607/1000000000)
  cRadius := (65042511/1000000000)

theorem lowTIParameters131_valid : Valid lowTIParameters131 := by
  constructor
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters131,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters131,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]
  · norm_num [lowTIParameters131]

theorem lowTISupply131 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters131 (1051/2000) (263/500) := by
  refine ⟨lowTIParameters131_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters131]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters131]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry131W hn hθ).1 (by norm_num [lowTIParameters131])
      (by norm_num [lowTIParameters131]) (by norm_num [lowTIParameters131])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry131C hn hθ).1 (by norm_num [lowTIParameters131])
      (by norm_num [lowTIParameters131]) (by norm_num [lowTIParameters131])
  · intro θ hθ
    exact (lowGeometry131W hn hθ).2
  · intro θ hθ
    exact (lowGeometry131C hn hθ).2

noncomputable def lowTIParameters132 : Parameters where
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
  wRadius := (29918279/250000000)
  cRadius := (813401/12500000)

theorem lowTIParameters132_valid : Valid lowTIParameters132 := by
  constructor
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters132,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters132,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]
  · norm_num [lowTIParameters132]

theorem lowTISupply132 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters132 (263/500) (1053/2000) := by
  refine ⟨lowTIParameters132_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters132]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters132]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry132W hn hθ).1 (by norm_num [lowTIParameters132])
      (by norm_num [lowTIParameters132]) (by norm_num [lowTIParameters132])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry132C hn hθ).1 (by norm_num [lowTIParameters132])
      (by norm_num [lowTIParameters132]) (by norm_num [lowTIParameters132])
  · intro θ hθ
    exact (lowGeometry132W hn hθ).2
  · intro θ hθ
    exact (lowGeometry132C hn hθ).2

noncomputable def lowTIParameters133 : Parameters where
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
  wRadius := (119719557/1000000000)
  cRadius := (65101617/1000000000)

theorem lowTIParameters133_valid : Valid lowTIParameters133 := by
  constructor
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters133,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters133,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]
  · norm_num [lowTIParameters133]

theorem lowTISupply133 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters133 (1053/2000) (527/1000) := by
  refine ⟨lowTIParameters133_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters133]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters133]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry133W hn hθ).1 (by norm_num [lowTIParameters133])
      (by norm_num [lowTIParameters133]) (by norm_num [lowTIParameters133])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry133C hn hθ).1 (by norm_num [lowTIParameters133])
      (by norm_num [lowTIParameters133]) (by norm_num [lowTIParameters133])
  · intro θ hθ
    exact (lowGeometry133W hn hθ).2
  · intro θ hθ
    exact (lowGeometry133C hn hθ).2

noncomputable def lowTIParameters134 : Parameters where
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
  wRadius := (119765931/1000000000)
  cRadius := (32565561/500000000)

theorem lowTIParameters134_valid : Valid lowTIParameters134 := by
  constructor
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters134,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters134,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]
  · norm_num [lowTIParameters134]

theorem lowTISupply134 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters134 (527/1000) (211/400) := by
  refine ⟨lowTIParameters134_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters134]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters134]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry134W hn hθ).1 (by norm_num [lowTIParameters134])
      (by norm_num [lowTIParameters134]) (by norm_num [lowTIParameters134])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry134C hn hθ).1 (by norm_num [lowTIParameters134])
      (by norm_num [lowTIParameters134]) (by norm_num [lowTIParameters134])
  · intro θ hθ
    exact (lowGeometry134W hn hθ).2
  · intro θ hθ
    exact (lowGeometry134C hn hθ).2

noncomputable def lowTIParameters135 : Parameters where
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
  wRadius := (59906119/500000000)
  cRadius := (32580297/500000000)

theorem lowTIParameters135_valid : Valid lowTIParameters135 := by
  constructor
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters135,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters135,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]
  · norm_num [lowTIParameters135]

theorem lowTISupply135 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters135 (211/400) (66/125) := by
  refine ⟨lowTIParameters135_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters135]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters135]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry135W hn hθ).1 (by norm_num [lowTIParameters135])
      (by norm_num [lowTIParameters135]) (by norm_num [lowTIParameters135])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry135C hn hθ).1 (by norm_num [lowTIParameters135])
      (by norm_num [lowTIParameters135]) (by norm_num [lowTIParameters135])
  · intro θ hθ
    exact (lowGeometry135W hn hθ).2
  · intro θ hθ
    exact (lowGeometry135C hn hθ).2

noncomputable def lowTIParameters136 : Parameters where
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
  wRadius := (59929239/500000000)
  cRadius := (32595017/500000000)

theorem lowTIParameters136_valid : Valid lowTIParameters136 := by
  constructor
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters136,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters136,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]
  · norm_num [lowTIParameters136]

theorem lowTISupply136 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters136 (66/125) (1057/2000) := by
  refine ⟨lowTIParameters136_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters136]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters136]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry136W hn hθ).1 (by norm_num [lowTIParameters136])
      (by norm_num [lowTIParameters136]) (by norm_num [lowTIParameters136])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry136C hn hθ).1 (by norm_num [lowTIParameters136])
      (by norm_num [lowTIParameters136]) (by norm_num [lowTIParameters136])
  · intro θ hθ
    exact (lowGeometry136W hn hθ).2
  · intro θ hθ
    exact (lowGeometry136C hn hθ).2

noncomputable def lowTIParameters137 : Parameters where
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
  wRadius := (2398093/20000000)
  cRadius := (32609721/500000000)

theorem lowTIParameters137_valid : Valid lowTIParameters137 := by
  constructor
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters137,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters137,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]
  · norm_num [lowTIParameters137]

theorem lowTISupply137 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters137 (1057/2000) (529/1000) := by
  refine ⟨lowTIParameters137_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters137]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters137]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry137W hn hθ).1 (by norm_num [lowTIParameters137])
      (by norm_num [lowTIParameters137]) (by norm_num [lowTIParameters137])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry137C hn hθ).1 (by norm_num [lowTIParameters137])
      (by norm_num [lowTIParameters137]) (by norm_num [lowTIParameters137])
  · intro θ hθ
    exact (lowGeometry137W hn hθ).2
  · intro θ hθ
    exact (lowGeometry137C hn hθ).2

noncomputable def lowTIParameters138 : Parameters where
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
  wRadius := (59975377/500000000)
  cRadius := (65248817/1000000000)

theorem lowTIParameters138_valid : Valid lowTIParameters138 := by
  constructor
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters138,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters138,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]
  · norm_num [lowTIParameters138]

theorem lowTISupply138 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters138 (529/1000) (1059/2000) := by
  refine ⟨lowTIParameters138_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters138]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters138]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry138W hn hθ).1 (by norm_num [lowTIParameters138])
      (by norm_num [lowTIParameters138]) (by norm_num [lowTIParameters138])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry138C hn hθ).1 (by norm_num [lowTIParameters138])
      (by norm_num [lowTIParameters138]) (by norm_num [lowTIParameters138])
  · intro θ hθ
    exact (lowGeometry138W hn hθ).2
  · intro θ hθ
    exact (lowGeometry138C hn hθ).2

noncomputable def lowTIParameters139 : Parameters where
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
  wRadius := (119996791/1000000000)
  cRadius := (815977/12500000)

theorem lowTIParameters139_valid : Valid lowTIParameters139 := by
  constructor
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · have h : √((((637130693/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (144976786983/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters139,ta_lam] at h ⊢
    linarith
  · have h : √((((115067499/200000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (192451220577/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters139,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]
  · norm_num [lowTIParameters139]

theorem lowTISupply139 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters139 (1059/2000) (53/100) := by
  refine ⟨lowTIParameters139_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum120W hn using 1 <;> norm_num [lowTIParameters139]
  · convert lowUniformNum120C hn using 1 <;> norm_num [lowTIParameters139]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry139W hn hθ).1 (by norm_num [lowTIParameters139])
      (by norm_num [lowTIParameters139]) (by norm_num [lowTIParameters139])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry139C hn hθ).1 (by norm_num [lowTIParameters139])
      (by norm_num [lowTIParameters139]) (by norm_num [lowTIParameters139])
  · intro θ hθ
    exact (lowGeometry139W hn hθ).2
  · intro θ hθ
    exact (lowGeometry139C hn hθ).2

noncomputable def lowTIParameters140 : Parameters where
  wlo := (30686227/100000000)
  whi := (334843829/500000000)
  clo := (382501131/1000000000)
  chi := (279629041/500000000)
  wE := (315619411/500000000)
  wS := (9/25)
  cE := (570281623/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (9965362239/15625000000)
  cLam := (575127741567/1000000000000)
  plane := (1/1)
  wRadius := (120042761/1000000000)
  cRadius := (6530747/100000000)

theorem lowTIParameters140_valid : Valid lowTIParameters140 := by
  constructor
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters140,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters140,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]
  · norm_num [lowTIParameters140]

theorem lowTISupply140 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters140 (53/100) (1061/2000) := by
  refine ⟨lowTIParameters140_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters140]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters140]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry140W hn hθ).1 (by norm_num [lowTIParameters140])
      (by norm_num [lowTIParameters140]) (by norm_num [lowTIParameters140])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry140C hn hθ).1 (by norm_num [lowTIParameters140])
      (by norm_num [lowTIParameters140]) (by norm_num [lowTIParameters140])
  · intro θ hθ
    exact (lowGeometry140W hn hθ).2
  · intro θ hθ
    exact (lowGeometry140C hn hθ).2

noncomputable def lowTIParameters141 : Parameters where
  wlo := (30686227/100000000)
  whi := (334843829/500000000)
  clo := (382501131/1000000000)
  chi := (279629041/500000000)
  wE := (315619411/500000000)
  wS := (9/25)
  cE := (570281623/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (9965362239/15625000000)
  cLam := (575127741567/1000000000000)
  plane := (1/1)
  wRadius := (15011083/125000000)
  cRadius := (16334187/250000000)

theorem lowTIParameters141_valid : Valid lowTIParameters141 := by
  constructor
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters141,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters141,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]
  · norm_num [lowTIParameters141]

theorem lowTISupply141 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters141 (1061/2000) (531/1000) := by
  refine ⟨lowTIParameters141_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters141]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters141]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry141W hn hθ).1 (by norm_num [lowTIParameters141])
      (by norm_num [lowTIParameters141]) (by norm_num [lowTIParameters141])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry141C hn hθ).1 (by norm_num [lowTIParameters141])
      (by norm_num [lowTIParameters141]) (by norm_num [lowTIParameters141])
  · intro θ hθ
    exact (lowGeometry141W hn hθ).2
  · intro θ hθ
    exact (lowGeometry141C hn hθ).2

noncomputable def lowTIParameters142 : Parameters where
  wlo := (30686227/100000000)
  whi := (334843829/500000000)
  clo := (382501131/1000000000)
  chi := (279629041/500000000)
  wE := (315619411/500000000)
  wS := (9/25)
  cE := (570281623/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (9965362239/15625000000)
  cLam := (575127741567/1000000000000)
  plane := (1/1)
  wRadius := (120134499/1000000000)
  cRadius := (32682997/500000000)

theorem lowTIParameters142_valid : Valid lowTIParameters142 := by
  constructor
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters142,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters142,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]
  · norm_num [lowTIParameters142]

theorem lowTISupply142 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters142 (531/1000) (1063/2000) := by
  refine ⟨lowTIParameters142_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters142]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters142]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry142W hn hθ).1 (by norm_num [lowTIParameters142])
      (by norm_num [lowTIParameters142]) (by norm_num [lowTIParameters142])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry142C hn hθ).1 (by norm_num [lowTIParameters142])
      (by norm_num [lowTIParameters142]) (by norm_num [lowTIParameters142])
  · intro θ hθ
    exact (lowGeometry142W hn hθ).2
  · intro θ hθ
    exact (lowGeometry142C hn hθ).2

noncomputable def lowTIParameters143 : Parameters where
  wlo := (30686227/100000000)
  whi := (334843829/500000000)
  clo := (382501131/1000000000)
  chi := (279629041/500000000)
  wE := (315619411/500000000)
  wS := (9/25)
  cE := (570281623/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (9965362239/15625000000)
  cLam := (575127741567/1000000000000)
  plane := (1/1)
  wRadius := (60090133/500000000)
  cRadius := (8174401/125000000)

theorem lowTIParameters143_valid : Valid lowTIParameters143 := by
  constructor
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters143,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters143,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]
  · norm_num [lowTIParameters143]

theorem lowTISupply143 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters143 (1063/2000) (133/250) := by
  refine ⟨lowTIParameters143_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters143]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters143]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry143W hn hθ).1 (by norm_num [lowTIParameters143])
      (by norm_num [lowTIParameters143]) (by norm_num [lowTIParameters143])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry143C hn hθ).1 (by norm_num [lowTIParameters143])
      (by norm_num [lowTIParameters143]) (by norm_num [lowTIParameters143])
  · intro θ hθ
    exact (lowGeometry143W hn hθ).2
  · intro θ hθ
    exact (lowGeometry143C hn hθ).2

end BstLean.BlueprintLow
