import BstLean.Part291GeometryBatch4
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters144 : Parameters where
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
  wRadius := (60112983/500000000)
  cRadius := (65424389/1000000000)

theorem lowTIParameters144_valid : Valid lowTIParameters144 := by
  constructor
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters144,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters144,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]
  · norm_num [lowTIParameters144]

theorem lowTISupply144 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters144 (133/250) (213/400) := by
  refine ⟨lowTIParameters144_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters144]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters144]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry144W hn hθ).1 (by norm_num [lowTIParameters144])
      (by norm_num [lowTIParameters144]) (by norm_num [lowTIParameters144])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry144C hn hθ).1 (by norm_num [lowTIParameters144])
      (by norm_num [lowTIParameters144]) (by norm_num [lowTIParameters144])
  · intro θ hθ
    exact (lowGeometry144W hn hθ).2
  · intro θ hθ
    exact (lowGeometry144C hn hθ).2

noncomputable def lowTIParameters145 : Parameters where
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
  wRadius := (120271599/1000000000)
  cRadius := (65453537/1000000000)

theorem lowTIParameters145_valid : Valid lowTIParameters145 := by
  constructor
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters145,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters145,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]
  · norm_num [lowTIParameters145]

theorem lowTISupply145 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters145 (213/400) (533/1000) := by
  refine ⟨lowTIParameters145_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters145]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters145]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry145W hn hθ).1 (by norm_num [lowTIParameters145])
      (by norm_num [lowTIParameters145]) (by norm_num [lowTIParameters145])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry145C hn hθ).1 (by norm_num [lowTIParameters145])
      (by norm_num [lowTIParameters145]) (by norm_num [lowTIParameters145])
  · intro θ hθ
    exact (lowGeometry145W hn hθ).2
  · intro θ hθ
    exact (lowGeometry145C hn hθ).2

noncomputable def lowTIParameters146 : Parameters where
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
  wRadius := (30079291/250000000)
  cRadius := (32741327/500000000)

theorem lowTIParameters146_valid : Valid lowTIParameters146 := by
  constructor
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters146,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters146,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]
  · norm_num [lowTIParameters146]

theorem lowTISupply146 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters146 (533/1000) (1067/2000) := by
  refine ⟨lowTIParameters146_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters146]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters146]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry146W hn hθ).1 (by norm_num [lowTIParameters146])
      (by norm_num [lowTIParameters146]) (by norm_num [lowTIParameters146])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry146C hn hθ).1 (by norm_num [lowTIParameters146])
      (by norm_num [lowTIParameters146]) (by norm_num [lowTIParameters146])
  · intro θ hθ
    exact (lowGeometry146W hn hθ).2
  · intro θ hθ
    exact (lowGeometry146C hn hθ).2

noncomputable def lowTIParameters147 : Parameters where
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
  wRadius := (60181331/500000000)
  cRadius := (65511737/1000000000)

theorem lowTIParameters147_valid : Valid lowTIParameters147 := by
  constructor
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters147,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters147,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]
  · norm_num [lowTIParameters147]

theorem lowTISupply147 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters147 (1067/2000) (267/500) := by
  refine ⟨lowTIParameters147_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters147]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters147]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry147W hn hθ).1 (by norm_num [lowTIParameters147])
      (by norm_num [lowTIParameters147]) (by norm_num [lowTIParameters147])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry147C hn hθ).1 (by norm_num [lowTIParameters147])
      (by norm_num [lowTIParameters147]) (by norm_num [lowTIParameters147])
  · intro θ hθ
    exact (lowGeometry147W hn hθ).2
  · intro θ hθ
    exact (lowGeometry147C hn hθ).2

noncomputable def lowTIParameters148 : Parameters where
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
  wRadius := (30102023/250000000)
  cRadius := (65540789/1000000000)

theorem lowTIParameters148_valid : Valid lowTIParameters148 := by
  constructor
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters148,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters148,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]
  · norm_num [lowTIParameters148]

theorem lowTISupply148 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters148 (267/500) (1069/2000) := by
  refine ⟨lowTIParameters148_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters148]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters148]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry148W hn hθ).1 (by norm_num [lowTIParameters148])
      (by norm_num [lowTIParameters148]) (by norm_num [lowTIParameters148])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry148C hn hθ).1 (by norm_num [lowTIParameters148])
      (by norm_num [lowTIParameters148]) (by norm_num [lowTIParameters148])
  · intro θ hθ
    exact (lowGeometry148W hn hθ).2
  · intro θ hθ
    exact (lowGeometry148C hn hθ).2

noncomputable def lowTIParameters149 : Parameters where
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
  wRadius := (60226727/500000000)
  cRadius := (4098113/62500000)

theorem lowTIParameters149_valid : Valid lowTIParameters149 := by
  constructor
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters149,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters149,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]
  · norm_num [lowTIParameters149]

theorem lowTISupply149 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters149 (1069/2000) (107/200) := by
  refine ⟨lowTIParameters149_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters149]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters149]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry149W hn hθ).1 (by norm_num [lowTIParameters149])
      (by norm_num [lowTIParameters149]) (by norm_num [lowTIParameters149])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry149C hn hθ).1 (by norm_num [lowTIParameters149])
      (by norm_num [lowTIParameters149]) (by norm_num [lowTIParameters149])
  · intro θ hθ
    exact (lowGeometry149W hn hθ).2
  · intro θ hθ
    exact (lowGeometry149C hn hθ).2

noncomputable def lowTIParameters150 : Parameters where
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
  wRadius := (96399/800000)
  cRadius := (13119759/200000000)

theorem lowTIParameters150_valid : Valid lowTIParameters150 := by
  constructor
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters150,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters150,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]
  · norm_num [lowTIParameters150]

theorem lowTISupply150 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters150 (107/200) (1071/2000) := by
  refine ⟨lowTIParameters150_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters150]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters150]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry150W hn hθ).1 (by norm_num [lowTIParameters150])
      (by norm_num [lowTIParameters150]) (by norm_num [lowTIParameters150])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry150C hn hθ).1 (by norm_num [lowTIParameters150])
      (by norm_num [lowTIParameters150]) (by norm_num [lowTIParameters150])
  · intro θ hθ
    exact (lowGeometry150W hn hθ).2
  · intro θ hθ
    exact (lowGeometry150C hn hθ).2

noncomputable def lowTIParameters151 : Parameters where
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
  wRadius := (120543977/1000000000)
  cRadius := (65627749/1000000000)

theorem lowTIParameters151_valid : Valid lowTIParameters151 := by
  constructor
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters151,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters151,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]
  · norm_num [lowTIParameters151]

theorem lowTISupply151 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters151 (1071/2000) (67/125) := by
  refine ⟨lowTIParameters151_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters151]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters151]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry151W hn hθ).1 (by norm_num [lowTIParameters151])
      (by norm_num [lowTIParameters151]) (by norm_num [lowTIParameters151])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry151C hn hθ).1 (by norm_num [lowTIParameters151])
      (by norm_num [lowTIParameters151]) (by norm_num [lowTIParameters151])
  · intro θ hθ
    exact (lowGeometry151W hn hθ).2
  · intro θ hθ
    exact (lowGeometry151C hn hθ).2

noncomputable def lowTIParameters152 : Parameters where
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
  wRadius := (120589137/1000000000)
  cRadius := (65656671/1000000000)

theorem lowTIParameters152_valid : Valid lowTIParameters152 := by
  constructor
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters152,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters152,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]
  · norm_num [lowTIParameters152]

theorem lowTISupply152 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters152 (67/125) (1073/2000) := by
  refine ⟨lowTIParameters152_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters152]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters152]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry152W hn hθ).1 (by norm_num [lowTIParameters152])
      (by norm_num [lowTIParameters152]) (by norm_num [lowTIParameters152])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry152C hn hθ).1 (by norm_num [lowTIParameters152])
      (by norm_num [lowTIParameters152]) (by norm_num [lowTIParameters152])
  · intro θ hθ
    exact (lowGeometry152W hn hθ).2
  · intro θ hθ
    exact (lowGeometry152C hn hθ).2

noncomputable def lowTIParameters153 : Parameters where
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
  wRadius := (120634229/1000000000)
  cRadius := (1642139/25000000)

theorem lowTIParameters153_valid : Valid lowTIParameters153 := by
  constructor
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters153,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters153,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]
  · norm_num [lowTIParameters153]

theorem lowTISupply153 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters153 (1073/2000) (537/1000) := by
  refine ⟨lowTIParameters153_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters153]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters153]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry153W hn hθ).1 (by norm_num [lowTIParameters153])
      (by norm_num [lowTIParameters153]) (by norm_num [lowTIParameters153])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry153C hn hθ).1 (by norm_num [lowTIParameters153])
      (by norm_num [lowTIParameters153]) (by norm_num [lowTIParameters153])
  · intro θ hθ
    exact (lowGeometry153W hn hθ).2
  · intro θ hθ
    exact (lowGeometry153C hn hθ).2

noncomputable def lowTIParameters154 : Parameters where
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
  wRadius := (60339627/500000000)
  cRadius := (65714417/1000000000)

theorem lowTIParameters154_valid : Valid lowTIParameters154 := by
  constructor
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters154,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters154,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]
  · norm_num [lowTIParameters154]

theorem lowTISupply154 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters154 (537/1000) (43/80) := by
  refine ⟨lowTIParameters154_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters154]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters154]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry154W hn hθ).1 (by norm_num [lowTIParameters154])
      (by norm_num [lowTIParameters154]) (by norm_num [lowTIParameters154])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry154C hn hθ).1 (by norm_num [lowTIParameters154])
      (by norm_num [lowTIParameters154]) (by norm_num [lowTIParameters154])
  · intro θ hθ
    exact (lowGeometry154W hn hθ).2
  · intro θ hθ
    exact (lowGeometry154C hn hθ).2

noncomputable def lowTIParameters155 : Parameters where
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
  wRadius := (120724211/1000000000)
  cRadius := (65743241/1000000000)

theorem lowTIParameters155_valid : Valid lowTIParameters155 := by
  constructor
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters155,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters155,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]
  · norm_num [lowTIParameters155]

theorem lowTISupply155 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters155 (43/80) (269/500) := by
  refine ⟨lowTIParameters155_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters155]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters155]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry155W hn hθ).1 (by norm_num [lowTIParameters155])
      (by norm_num [lowTIParameters155]) (by norm_num [lowTIParameters155])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry155C hn hθ).1 (by norm_num [lowTIParameters155])
      (by norm_num [lowTIParameters155]) (by norm_num [lowTIParameters155])
  · intro θ hθ
    exact (lowGeometry155W hn hθ).2
  · intro θ hθ
    exact (lowGeometry155C hn hθ).2

noncomputable def lowTIParameters156 : Parameters where
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
  wRadius := (120769101/1000000000)
  cRadius := (65772033/1000000000)

theorem lowTIParameters156_valid : Valid lowTIParameters156 := by
  constructor
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters156,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters156,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]
  · norm_num [lowTIParameters156]

theorem lowTISupply156 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters156 (269/500) (1077/2000) := by
  refine ⟨lowTIParameters156_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters156]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters156]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry156W hn hθ).1 (by norm_num [lowTIParameters156])
      (by norm_num [lowTIParameters156]) (by norm_num [lowTIParameters156])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry156C hn hθ).1 (by norm_num [lowTIParameters156])
      (by norm_num [lowTIParameters156]) (by norm_num [lowTIParameters156])
  · intro θ hθ
    exact (lowGeometry156W hn hθ).2
  · intro θ hθ
    exact (lowGeometry156C hn hθ).2

noncomputable def lowTIParameters157 : Parameters where
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
  wRadius := (120813923/1000000000)
  cRadius := (65800793/1000000000)

theorem lowTIParameters157_valid : Valid lowTIParameters157 := by
  constructor
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters157,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters157,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]
  · norm_num [lowTIParameters157]

theorem lowTISupply157 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters157 (1077/2000) (539/1000) := by
  refine ⟨lowTIParameters157_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters157]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters157]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry157W hn hθ).1 (by norm_num [lowTIParameters157])
      (by norm_num [lowTIParameters157]) (by norm_num [lowTIParameters157])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry157C hn hθ).1 (by norm_num [lowTIParameters157])
      (by norm_num [lowTIParameters157]) (by norm_num [lowTIParameters157])
  · intro θ hθ
    exact (lowGeometry157W hn hθ).2
  · intro θ hθ
    exact (lowGeometry157C hn hθ).2

noncomputable def lowTIParameters158 : Parameters where
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
  wRadius := (120858677/1000000000)
  cRadius := (822869/12500000)

theorem lowTIParameters158_valid : Valid lowTIParameters158 := by
  constructor
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters158,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters158,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]
  · norm_num [lowTIParameters158]

theorem lowTISupply158 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters158 (539/1000) (1079/2000) := by
  refine ⟨lowTIParameters158_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters158]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters158]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry158W hn hθ).1 (by norm_num [lowTIParameters158])
      (by norm_num [lowTIParameters158]) (by norm_num [lowTIParameters158])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry158C hn hθ).1 (by norm_num [lowTIParameters158])
      (by norm_num [lowTIParameters158]) (by norm_num [lowTIParameters158])
  · intro θ hθ
    exact (lowGeometry158W hn hθ).2
  · intro θ hθ
    exact (lowGeometry158C hn hθ).2

noncomputable def lowTIParameters159 : Parameters where
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
  wRadius := (30225841/250000000)
  cRadius := (32929107/500000000)

theorem lowTIParameters159_valid : Valid lowTIParameters159 := by
  constructor
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · have h : √((((315619411/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (17770471537/125000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters159,ta_lam] at h ⊢
    linarith
  · have h : √((((570281623/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (189986930067/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters159,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]
  · norm_num [lowTIParameters159]

theorem lowTISupply159 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters159 (1079/2000) (27/50) := by
  refine ⟨lowTIParameters159_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum140W hn using 1 <;> norm_num [lowTIParameters159]
  · convert lowUniformNum140C hn using 1 <;> norm_num [lowTIParameters159]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry159W hn hθ).1 (by norm_num [lowTIParameters159])
      (by norm_num [lowTIParameters159]) (by norm_num [lowTIParameters159])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry159C hn hθ).1 (by norm_num [lowTIParameters159])
      (by norm_num [lowTIParameters159]) (by norm_num [lowTIParameters159])
  · intro θ hθ
    exact (lowGeometry159W hn hθ).2
  · intro θ hθ
    exact (lowGeometry159C hn hθ).2

end BstLean.BlueprintLow
