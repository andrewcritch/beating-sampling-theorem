import BstLean.Part291GeometryBatch0
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters0 : Parameters where
  wlo := (193409909/500000000)
  whi := (367683783/500000000)
  clo := (57745557/125000000)
  chi := (125645833/200000000)
  wE := (674021631/1000000000)
  wS := (9/25)
  cE := (7587393/12500000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (42481737679/62500000000)
  cLam := (305705088671/500000000000)
  plane := (1/1)
  wRadius := (28238341/250000000)
  cRadius := (60890259/1000000000)

theorem lowTIParameters0_valid : Valid lowTIParameters0 := by
  constructor
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · have h : √((((674021631/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40674246841/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters0,ta_lam] at h ⊢
    linarith
  · have h : √((((7587393/12500000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (103957228671/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters0,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]
  · norm_num [lowTIParameters0]

theorem lowTISupply0 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters0 (23/50) (921/2000) := by
  refine ⟨lowTIParameters0_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum0W hn using 1 <;> norm_num [lowTIParameters0]
  · convert lowUniformNum0C hn using 1 <;> norm_num [lowTIParameters0]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry0W hn hθ).1 (by norm_num [lowTIParameters0])
      (by norm_num [lowTIParameters0]) (by norm_num [lowTIParameters0])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry0C hn hθ).1 (by norm_num [lowTIParameters0])
      (by norm_num [lowTIParameters0]) (by norm_num [lowTIParameters0])
  · intro θ hθ
    exact (lowGeometry0W hn hθ).2
  · intro θ hθ
    exact (lowGeometry0C hn hθ).2

noncomputable def lowTIParameters1 : Parameters where
  wlo := (193153297/500000000)
  whi := (734911287/1000000000)
  clo := (461458779/1000000000)
  chi := (39233919/62500000)
  wE := (673702321/1000000000)
  wS := (9/25)
  cE := (606717581/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (135878815621/200000000000)
  cLam := (611139230357/1000000000000)
  plane := (1/1)
  wRadius := (113008677/1000000000)
  cRadius := (12184811/200000000)

theorem lowTIParameters1_valid : Valid lowTIParameters1 := by
  constructor
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · have h : √((((673702321/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (32508583521/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters1,ta_lam] at h ⊢
    linarith
  · have h : √((((606717581/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (207780439857/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters1,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]
  · norm_num [lowTIParameters1]

theorem lowTISupply1 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters1 (921/2000) (461/1000) := by
  refine ⟨lowTIParameters1_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum1W hn using 1 <;> norm_num [lowTIParameters1]
  · convert lowUniformNum1C hn using 1 <;> norm_num [lowTIParameters1]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry1W hn hθ).1 (by norm_num [lowTIParameters1])
      (by norm_num [lowTIParameters1]) (by norm_num [lowTIParameters1])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry1C hn hθ).1 (by norm_num [lowTIParameters1])
      (by norm_num [lowTIParameters1]) (by norm_num [lowTIParameters1])
  · intro θ hθ
    exact (lowGeometry1W hn hθ).2
  · intro θ hθ
    exact (lowGeometry1C hn hθ).2

noncomputable def lowTIParameters2 : Parameters where
  wlo := (385280557/1000000000)
  whi := (734454819/1000000000)
  clo := (230223829/500000000)
  chi := (627256151/1000000000)
  wE := (673383227/1000000000)
  wS := (9/25)
  cE := (606443903/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (679080576347/1000000000000)
  cLam := (610868466243/1000000000000)
  plane := (1/1)
  wRadius := (113063923/1000000000)
  cRadius := (30478909/500000000)

theorem lowTIParameters2_valid : Valid lowTIParameters2 := by
  constructor
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · have h : √((((673383227/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (162388962847/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters2,ta_lam] at h ⊢
    linarith
  · have h : √((((606443903/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (207646514743/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters2,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]
  · norm_num [lowTIParameters2]

theorem lowTISupply2 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters2 (461/1000) (923/2000) := by
  refine ⟨lowTIParameters2_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum2W hn using 1 <;> norm_num [lowTIParameters2]
  · convert lowUniformNum2C hn using 1 <;> norm_num [lowTIParameters2]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry2W hn hθ).1 (by norm_num [lowTIParameters2])
      (by norm_num [lowTIParameters2]) (by norm_num [lowTIParameters2])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry2C hn hθ).1 (by norm_num [lowTIParameters2])
      (by norm_num [lowTIParameters2]) (by norm_num [lowTIParameters2])
  · intro θ hθ
    exact (lowGeometry2W hn hθ).2
  · intro θ hθ
    exact (lowGeometry2C hn hθ).2

noncomputable def lowTIParameters3 : Parameters where
  wlo := (385280557/1000000000)
  whi := (734454819/1000000000)
  clo := (230223829/500000000)
  chi := (627256151/1000000000)
  wE := (673383227/1000000000)
  wS := (9/25)
  cE := (606443903/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (679080576347/1000000000000)
  cLam := (610868466243/1000000000000)
  plane := (1/1)
  wRadius := (113119101/1000000000)
  cRadius := (15247887/250000000)

theorem lowTIParameters3_valid : Valid lowTIParameters3 := by
  constructor
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · have h : √((((673383227/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (162388962847/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters3,ta_lam] at h ⊢
    linarith
  · have h : √((((606443903/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (207646514743/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters3,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]
  · norm_num [lowTIParameters3]

theorem lowTISupply3 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters3 (923/2000) (231/500) := by
  refine ⟨lowTIParameters3_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum2W hn using 1 <;> norm_num [lowTIParameters3]
  · convert lowUniformNum2C hn using 1 <;> norm_num [lowTIParameters3]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry3W hn hθ).1 (by norm_num [lowTIParameters3])
      (by norm_num [lowTIParameters3]) (by norm_num [lowTIParameters3])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry3C hn hθ).1 (by norm_num [lowTIParameters3])
      (by norm_num [lowTIParameters3]) (by norm_num [lowTIParameters3])
  · intro θ hθ
    exact (lowGeometry3W hn hθ).2
  · intro θ hθ
    exact (lowGeometry3C hn hθ).2

noncomputable def lowTIParameters4 : Parameters where
  wlo := (96063767/250000000)
  whi := (733541317/1000000000)
  clo := (28714803/62500000)
  chi := (626282771/1000000000)
  wE := (672745683/1000000000)
  wS := (9/25)
  cE := (302948543/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (678454237941/1000000000000)
  cLam := (610327482671/1000000000000)
  plane := (1/1)
  wRadius := (113174211/1000000000)
  cRadius := (30512623/500000000)

theorem lowTIParameters4_valid : Valid lowTIParameters4 := by
  constructor
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · have h : √((((672745683/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (162081396441/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters4,ta_lam] at h ⊢
    linarith
  · have h : √((((302948543/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (207378939671/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters4,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]
  · norm_num [lowTIParameters4]

theorem lowTISupply4 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters4 (231/500) (37/80) := by
  refine ⟨lowTIParameters4_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum4W hn using 1 <;> norm_num [lowTIParameters4]
  · convert lowUniformNum4C hn using 1 <;> norm_num [lowTIParameters4]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry4W hn hθ).1 (by norm_num [lowTIParameters4])
      (by norm_num [lowTIParameters4]) (by norm_num [lowTIParameters4])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry4C hn hθ).1 (by norm_num [lowTIParameters4])
      (by norm_num [lowTIParameters4]) (by norm_num [lowTIParameters4])
  · intro θ hθ
    exact (lowGeometry4W hn hθ).2
  · intro θ hθ
    exact (lowGeometry4C hn hθ).2

noncomputable def lowTIParameters5 : Parameters where
  wlo := (96063767/250000000)
  whi := (733541317/1000000000)
  clo := (28714803/62500000)
  chi := (626282771/1000000000)
  wE := (672745683/1000000000)
  wS := (9/25)
  cE := (302948543/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (678454237941/1000000000000)
  cLam := (610327482671/1000000000000)
  plane := (1/1)
  wRadius := (56614627/500000000)
  cRadius := (1908091/31250000)

theorem lowTIParameters5_valid : Valid lowTIParameters5 := by
  constructor
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · have h : √((((672745683/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (162081396441/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters5,ta_lam] at h ⊢
    linarith
  · have h : √((((302948543/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (207378939671/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters5,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]
  · norm_num [lowTIParameters5]

theorem lowTISupply5 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters5 (37/80) (463/1000) := by
  refine ⟨lowTIParameters5_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum4W hn using 1 <;> norm_num [lowTIParameters5]
  · convert lowUniformNum4C hn using 1 <;> norm_num [lowTIParameters5]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry5W hn hθ).1 (by norm_num [lowTIParameters5])
      (by norm_num [lowTIParameters5]) (by norm_num [lowTIParameters5])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry5C hn hθ).1 (by norm_num [lowTIParameters5])
      (by norm_num [lowTIParameters5]) (by norm_num [lowTIParameters5])
  · intro θ hθ
    exact (lowGeometry5W hn hθ).2
  · intro θ hθ
    exact (lowGeometry5C hn hθ).2

noncomputable def lowTIParameters6 : Parameters where
  wlo := (191615063/500000000)
  whi := (366313529/500000000)
  clo := (458426349/1000000000)
  chi := (156327257/250000000)
  wE := (336054497/500000000)
  wS := (9/25)
  cE := (60535099/100000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (169457195701/250000000000)
  cLam := (121957445523/200000000000)
  plane := (1/1)
  wRadius := (113284229/1000000000)
  cRadius := (12218509/200000000)

theorem lowTIParameters6_valid : Valid lowTIParameters6 := by
  constructor
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · have h : √((((336054497/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40443571451/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters6,ta_lam] at h ⊢
    linarith
  · have h : √((((60535099/100000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (41422346523/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters6,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]
  · norm_num [lowTIParameters6]

theorem lowTISupply6 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters6 (463/1000) (927/2000) := by
  refine ⟨lowTIParameters6_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum6W hn using 1 <;> norm_num [lowTIParameters6]
  · convert lowUniformNum6C hn using 1 <;> norm_num [lowTIParameters6]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry6W hn hθ).1 (by norm_num [lowTIParameters6])
      (by norm_num [lowTIParameters6]) (by norm_num [lowTIParameters6])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry6C hn hθ).1 (by norm_num [lowTIParameters6])
      (by norm_num [lowTIParameters6]) (by norm_num [lowTIParameters6])
  · intro θ hθ
    exact (lowGeometry6W hn hθ).2
  · intro θ hθ
    exact (lowGeometry6C hn hθ).2

noncomputable def lowTIParameters7 : Parameters where
  wlo := (191615063/500000000)
  whi := (366313529/500000000)
  clo := (458426349/1000000000)
  chi := (156327257/250000000)
  wE := (336054497/500000000)
  wS := (9/25)
  cE := (60535099/100000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (169457195701/250000000000)
  cLam := (121957445523/200000000000)
  plane := (1/1)
  wRadius := (113339137/1000000000)
  cRadius := (30563073/500000000)

theorem lowTIParameters7_valid : Valid lowTIParameters7 := by
  constructor
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · have h : √((((336054497/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40443571451/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters7,ta_lam] at h ⊢
    linarith
  · have h : √((((60535099/100000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (41422346523/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters7,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]
  · norm_num [lowTIParameters7]

theorem lowTISupply7 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters7 (927/2000) (58/125) := by
  refine ⟨lowTIParameters7_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum6W hn using 1 <;> norm_num [lowTIParameters7]
  · convert lowUniformNum6C hn using 1 <;> norm_num [lowTIParameters7]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry7W hn hθ).1 (by norm_num [lowTIParameters7])
      (by norm_num [lowTIParameters7]) (by norm_num [lowTIParameters7])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry7C hn hθ).1 (by norm_num [lowTIParameters7])
      (by norm_num [lowTIParameters7]) (by norm_num [lowTIParameters7])
  · intro θ hθ
    exact (lowGeometry7W hn hθ).2
  · intro θ hθ
    exact (lowGeometry7C hn hθ).2

noncomputable def lowTIParameters8 : Parameters where
  wlo := (38220573/100000000)
  whi := (146342409/200000000)
  clo := (457416159/1000000000)
  chi := (15608373/25000000)
  wE := (335736579/500000000)
  wS := (9/25)
  cE := (604805611/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (169301052261/250000000000)
  cLam := (152311924279/250000000000)
  plane := (1/1)
  wRadius := (113393977/1000000000)
  cRadius := (30579857/500000000)

theorem lowTIParameters8_valid : Valid lowTIParameters8 := by
  constructor
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · have h : √((((335736579/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40366907511/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters8,ta_lam] at h ⊢
    linarith
  · have h : √((((604805611/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (6463902863/31250000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters8,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]
  · norm_num [lowTIParameters8]

theorem lowTISupply8 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters8 (58/125) (929/2000) := by
  refine ⟨lowTIParameters8_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum8W hn using 1 <;> norm_num [lowTIParameters8]
  · convert lowUniformNum8C hn using 1 <;> norm_num [lowTIParameters8]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry8W hn hθ).1 (by norm_num [lowTIParameters8])
      (by norm_num [lowTIParameters8]) (by norm_num [lowTIParameters8])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry8C hn hθ).1 (by norm_num [lowTIParameters8])
      (by norm_num [lowTIParameters8]) (by norm_num [lowTIParameters8])
  · intro θ hθ
    exact (lowGeometry8W hn hθ).2
  · intro θ hθ
    exact (lowGeometry8C hn hθ).2

noncomputable def lowTIParameters9 : Parameters where
  wlo := (38220573/100000000)
  whi := (146342409/200000000)
  clo := (457416159/1000000000)
  chi := (15608373/25000000)
  wE := (335736579/500000000)
  wS := (9/25)
  cE := (604805611/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (169301052261/250000000000)
  cLam := (152311924279/250000000000)
  plane := (1/1)
  wRadius := (90759/800000)
  cRadius := (244773/4000000)

theorem lowTIParameters9_valid : Valid lowTIParameters9 := by
  constructor
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · have h : √((((335736579/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40366907511/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters9,ta_lam] at h ⊢
    linarith
  · have h : √((((604805611/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (6463902863/31250000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters9,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]
  · norm_num [lowTIParameters9]

theorem lowTISupply9 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters9 (929/2000) (93/200) := by
  refine ⟨lowTIParameters9_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum8W hn using 1 <;> norm_num [lowTIParameters9]
  · convert lowUniformNum8C hn using 1 <;> norm_num [lowTIParameters9]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry9W hn hθ).1 (by norm_num [lowTIParameters9])
      (by norm_num [lowTIParameters9]) (by norm_num [lowTIParameters9])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry9C hn hθ).1 (by norm_num [lowTIParameters9])
      (by norm_num [lowTIParameters9]) (by norm_num [lowTIParameters9])
  · intro θ hθ
    exact (lowGeometry9W hn hθ).2
  · intro θ hθ
    exact (lowGeometry9C hn hθ).2

noncomputable def lowTIParameters10 : Parameters where
  wlo := (381181879/1000000000)
  whi := (730796277/1000000000)
  clo := (228203139/500000000)
  chi := (9740007/15625000)
  wE := (67083817/100000000)
  wS := (9/25)
  cE := (302130473/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (676580511823/1000000000000)
  cLam := (121741777641/200000000000)
  plane := (1/1)
  wRadius := (56751727/500000000)
  cRadius := (61226753/1000000000)

theorem lowTIParameters10_valid : Valid lowTIParameters10 := by
  constructor
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · have h : √((((67083817/100000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (161161426823/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters10,ta_lam] at h ⊢
    linarith
  · have h : √((((302130473/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (41315683041/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters10,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]
  · norm_num [lowTIParameters10]

theorem lowTISupply10 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters10 (93/200) (931/2000) := by
  refine ⟨lowTIParameters10_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum10W hn using 1 <;> norm_num [lowTIParameters10]
  · convert lowUniformNum10C hn using 1 <;> norm_num [lowTIParameters10]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry10W hn hθ).1 (by norm_num [lowTIParameters10])
      (by norm_num [lowTIParameters10]) (by norm_num [lowTIParameters10])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry10C hn hθ).1 (by norm_num [lowTIParameters10])
      (by norm_num [lowTIParameters10]) (by norm_num [lowTIParameters10])
  · intro θ hθ
    exact (lowGeometry10W hn hθ).2
  · intro θ hθ
    exact (lowGeometry10C hn hθ).2

noncomputable def lowTIParameters11 : Parameters where
  wlo := (381181879/1000000000)
  whi := (730796277/1000000000)
  clo := (228203139/500000000)
  chi := (9740007/15625000)
  wE := (67083817/100000000)
  wS := (9/25)
  cE := (302130473/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (676580511823/1000000000000)
  cLam := (121741777641/200000000000)
  plane := (1/1)
  wRadius := (28389523/250000000)
  cRadius := (957191/15625000)

theorem lowTIParameters11_valid : Valid lowTIParameters11 := by
  constructor
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · have h : √((((67083817/100000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (161161426823/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters11,ta_lam] at h ⊢
    linarith
  · have h : √((((302130473/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (41315683041/200000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters11,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]
  · norm_num [lowTIParameters11]

theorem lowTISupply11 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters11 (931/2000) (233/500) := by
  refine ⟨lowTIParameters11_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum10W hn using 1 <;> norm_num [lowTIParameters11]
  · convert lowUniformNum10C hn using 1 <;> norm_num [lowTIParameters11]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry11W hn hθ).1 (by norm_num [lowTIParameters11])
      (by norm_num [lowTIParameters11]) (by norm_num [lowTIParameters11])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry11C hn hθ).1 (by norm_num [lowTIParameters11])
      (by norm_num [lowTIParameters11]) (by norm_num [lowTIParameters11])
  · intro θ hθ
    exact (lowGeometry11W hn hθ).2
  · intro θ hθ
    exact (lowGeometry11C hn hθ).2

noncomputable def lowTIParameters12 : Parameters where
  wlo := (95039643/250000000)
  whi := (729879757/1000000000)
  clo := (455396707/1000000000)
  chi := (622385613/1000000000)
  wE := (670204029/1000000000)
  wS := (9/25)
  cE := (603716993/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (84494711279/125000000000)
  cLam := (608170798903/1000000000000)
  plane := (1/1)
  wRadius := (56806331/500000000)
  cRadius := (61293663/1000000000)

theorem lowTIParameters12_valid : Valid lowTIParameters12 := by
  constructor
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · have h : √((((670204029/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40213918933/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters12,ta_lam] at h ⊢
    linarith
  · have h : √((((603716993/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (206312302403/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters12,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]
  · norm_num [lowTIParameters12]

theorem lowTISupply12 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters12 (233/500) (933/2000) := by
  refine ⟨lowTIParameters12_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum12W hn using 1 <;> norm_num [lowTIParameters12]
  · convert lowUniformNum12C hn using 1 <;> norm_num [lowTIParameters12]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry12W hn hθ).1 (by norm_num [lowTIParameters12])
      (by norm_num [lowTIParameters12]) (by norm_num [lowTIParameters12])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry12C hn hθ).1 (by norm_num [lowTIParameters12])
      (by norm_num [lowTIParameters12]) (by norm_num [lowTIParameters12])
  · intro θ hθ
    exact (lowGeometry12W hn hθ).2
  · intro θ hθ
    exact (lowGeometry12C hn hθ).2

noncomputable def lowTIParameters13 : Parameters where
  wlo := (95039643/250000000)
  whi := (729879757/1000000000)
  clo := (455396707/1000000000)
  chi := (622385613/1000000000)
  wE := (670204029/1000000000)
  wS := (9/25)
  cE := (603716993/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (84494711279/125000000000)
  cLam := (608170798903/1000000000000)
  plane := (1/1)
  wRadius := (28416791/250000000)
  cRadius := (61327069/1000000000)

theorem lowTIParameters13_valid : Valid lowTIParameters13 := by
  constructor
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · have h : √((((670204029/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (40213918933/250000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters13,ta_lam] at h ⊢
    linarith
  · have h : √((((603716993/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (206312302403/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters13,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]
  · norm_num [lowTIParameters13]

theorem lowTISupply13 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters13 (933/2000) (467/1000) := by
  refine ⟨lowTIParameters13_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum12W hn using 1 <;> norm_num [lowTIParameters13]
  · convert lowUniformNum12C hn using 1 <;> norm_num [lowTIParameters13]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry13W hn hθ).1 (by norm_num [lowTIParameters13])
      (by norm_num [lowTIParameters13]) (by norm_num [lowTIParameters13])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry13C hn hθ).1 (by norm_num [lowTIParameters13])
      (by norm_num [lowTIParameters13]) (by norm_num [lowTIParameters13])
  · intro θ hθ
    exact (lowGeometry13W hn hθ).2
  · intro θ hθ
    exact (lowGeometry13C hn hθ).2

noncomputable def lowTIParameters14 : Parameters where
  wlo := (5923997/15625000)
  whi := (728962483/1000000000)
  clo := (454387443/1000000000)
  chi := (38838151/62500000)
  wE := (669570729/1000000000)
  wS := (9/25)
  cE := (482539/800000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (337667869227/500000000000)
  cLam := (607633427229/1000000000000)
  plane := (1/1)
  wRadius := (113721599/1000000000)
  cRadius := (30680221/500000000)

theorem lowTIParameters14_valid : Valid lowTIParameters14 := by
  constructor
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · have h : √((((669570729/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (80275186977/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters14,ta_lam] at h ⊢
    linarith
  · have h : √((((482539/800000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (206046552229/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters14,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]
  · norm_num [lowTIParameters14]

theorem lowTISupply14 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters14 (467/1000) (187/400) := by
  refine ⟨lowTIParameters14_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum14W hn using 1 <;> norm_num [lowTIParameters14]
  · convert lowUniformNum14C hn using 1 <;> norm_num [lowTIParameters14]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry14W hn hθ).1 (by norm_num [lowTIParameters14])
      (by norm_num [lowTIParameters14]) (by norm_num [lowTIParameters14])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry14C hn hθ).1 (by norm_num [lowTIParameters14])
      (by norm_num [lowTIParameters14]) (by norm_num [lowTIParameters14])
  · intro θ hθ
    exact (lowGeometry14W hn hθ).2
  · intro θ hθ
    exact (lowGeometry14C hn hθ).2

noncomputable def lowTIParameters15 : Parameters where
  wlo := (5923997/15625000)
  whi := (728962483/1000000000)
  clo := (454387443/1000000000)
  chi := (38838151/62500000)
  wE := (669570729/1000000000)
  wS := (9/25)
  cE := (482539/800000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (337667869227/500000000000)
  cLam := (607633427229/1000000000000)
  plane := (1/1)
  wRadius := (56887983/500000000)
  cRadius := (7674223/125000000)

theorem lowTIParameters15_valid : Valid lowTIParameters15 := by
  constructor
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · have h : √((((669570729/1000000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (80275186977/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters15,ta_lam] at h ⊢
    linarith
  · have h : √((((482539/800000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (206046552229/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters15,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]
  · norm_num [lowTIParameters15]

theorem lowTISupply15 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters15 (187/400) (117/250) := by
  refine ⟨lowTIParameters15_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum14W hn using 1 <;> norm_num [lowTIParameters15]
  · convert lowUniformNum14C hn using 1 <;> norm_num [lowTIParameters15]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry15W hn hθ).1 (by norm_num [lowTIParameters15])
      (by norm_num [lowTIParameters15]) (by norm_num [lowTIParameters15])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry15C hn hθ).1 (by norm_num [lowTIParameters15])
      (by norm_num [lowTIParameters15]) (by norm_num [lowTIParameters15])
  · intro θ hθ
    exact (lowGeometry15W hn hθ).2
  · intro θ hθ
    exact (lowGeometry15C hn hθ).2

end BstLean.BlueprintLow
