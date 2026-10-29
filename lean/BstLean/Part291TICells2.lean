import BstLean.Part291GeometryBatch1
import BstLean.Part291TIEvents
import BstLean.Part291Band
namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part255 BstLean.Part182
noncomputable def lowTIParameters32 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114689899/1000000000)
  cRadius := (15488909/250000000)

theorem lowTIParameters32_valid : Valid lowTIParameters32 := by
  constructor
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters32,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters32,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]
  · norm_num [lowTIParameters32]

theorem lowTISupply32 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters32 (119/250) (953/2000) := by
  refine ⟨lowTIParameters32_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters32]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters32]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry32W hn hθ).1 (by norm_num [lowTIParameters32])
      (by norm_num [lowTIParameters32]) (by norm_num [lowTIParameters32])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry32C hn hθ).1 (by norm_num [lowTIParameters32])
      (by norm_num [lowTIParameters32]) (by norm_num [lowTIParameters32])
  · intro θ hθ
    exact (lowGeometry32W hn hθ).2
  · intro θ hθ
    exact (lowGeometry32C hn hθ).2

noncomputable def lowTIParameters33 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (57371527/500000000)
  cRadius := (15497099/250000000)

theorem lowTIParameters33_valid : Valid lowTIParameters33 := by
  constructor
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters33,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters33,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]
  · norm_num [lowTIParameters33]

theorem lowTISupply33 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters33 (953/2000) (477/1000) := by
  refine ⟨lowTIParameters33_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters33]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters33]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry33W hn hθ).1 (by norm_num [lowTIParameters33])
      (by norm_num [lowTIParameters33]) (by norm_num [lowTIParameters33])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry33C hn hθ).1 (by norm_num [lowTIParameters33])
      (by norm_num [lowTIParameters33]) (by norm_num [lowTIParameters33])
  · intro θ hθ
    exact (lowGeometry33W hn hθ).2
  · intro θ hθ
    exact (lowGeometry33C hn hθ).2

noncomputable def lowTIParameters34 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (114796141/1000000000)
  cRadius := (62021123/1000000000)

theorem lowTIParameters34_valid : Valid lowTIParameters34 := by
  constructor
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters34,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters34,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]
  · norm_num [lowTIParameters34]

theorem lowTISupply34 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters34 (477/1000) (191/400) := by
  refine ⟨lowTIParameters34_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters34]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters34]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry34W hn hθ).1 (by norm_num [lowTIParameters34])
      (by norm_num [lowTIParameters34]) (by norm_num [lowTIParameters34])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry34C hn hθ).1 (by norm_num [lowTIParameters34])
      (by norm_num [lowTIParameters34]) (by norm_num [lowTIParameters34])
  · intro θ hθ
    exact (lowGeometry34W hn hθ).2
  · intro θ hθ
    exact (lowGeometry34C hn hθ).2

noncomputable def lowTIParameters35 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (57424581/500000000)
  cRadius := (62053817/1000000000)

theorem lowTIParameters35_valid : Valid lowTIParameters35 := by
  constructor
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters35,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters35,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]
  · norm_num [lowTIParameters35]

theorem lowTISupply35 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters35 (191/400) (239/500) := by
  refine ⟨lowTIParameters35_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters35]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters35]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry35W hn hθ).1 (by norm_num [lowTIParameters35])
      (by norm_num [lowTIParameters35]) (by norm_num [lowTIParameters35])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry35C hn hθ).1 (by norm_num [lowTIParameters35])
      (by norm_num [lowTIParameters35]) (by norm_num [lowTIParameters35])
  · intro θ hθ
    exact (lowGeometry35W hn hθ).2
  · intro θ hθ
    exact (lowGeometry35C hn hθ).2

noncomputable def lowTIParameters36 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (22980423/200000000)
  cRadius := (776081/12500000)

theorem lowTIParameters36_valid : Valid lowTIParameters36 := by
  constructor
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters36,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters36,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]
  · norm_num [lowTIParameters36]

theorem lowTISupply36 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters36 (239/500) (957/2000) := by
  refine ⟨lowTIParameters36_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters36]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters36]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry36W hn hθ).1 (by norm_num [lowTIParameters36])
      (by norm_num [lowTIParameters36]) (by norm_num [lowTIParameters36])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry36C hn hθ).1 (by norm_num [lowTIParameters36])
      (by norm_num [lowTIParameters36]) (by norm_num [lowTIParameters36])
  · intro θ hθ
    exact (lowGeometry36W hn hθ).2
  · intro θ hθ
    exact (lowGeometry36C hn hθ).2

noncomputable def lowTIParameters37 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (22991/200000)
  cRadius := (6211911/100000000)

theorem lowTIParameters37_valid : Valid lowTIParameters37 := by
  constructor
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters37,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters37,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]
  · norm_num [lowTIParameters37]

theorem lowTISupply37 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters37 (957/2000) (479/1000) := by
  refine ⟨lowTIParameters37_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters37]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters37]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry37W hn hθ).1 (by norm_num [lowTIParameters37])
      (by norm_num [lowTIParameters37]) (by norm_num [lowTIParameters37])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry37C hn hθ).1 (by norm_num [lowTIParameters37])
      (by norm_num [lowTIParameters37]) (by norm_num [lowTIParameters37])
  · intro θ hθ
    exact (lowGeometry37W hn hθ).2
  · intro θ hθ
    exact (lowGeometry37C hn hθ).2

noncomputable def lowTIParameters38 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (115007819/1000000000)
  cRadius := (15537927/250000000)

theorem lowTIParameters38_valid : Valid lowTIParameters38 := by
  constructor
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters38,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters38,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]
  · norm_num [lowTIParameters38]

theorem lowTISupply38 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters38 (479/1000) (959/2000) := by
  refine ⟨lowTIParameters38_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters38]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters38]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry38W hn hθ).1 (by norm_num [lowTIParameters38])
      (by norm_num [lowTIParameters38]) (by norm_num [lowTIParameters38])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry38C hn hθ).1 (by norm_num [lowTIParameters38])
      (by norm_num [lowTIParameters38]) (by norm_num [lowTIParameters38])
  · intro θ hθ
    exact (lowGeometry38W hn hθ).2
  · intro θ hθ
    exact (lowGeometry38C hn hθ).2

noncomputable def lowTIParameters39 : Parameters where
  wlo := (366904611/1000000000)
  whi := (726206157/1000000000)
  clo := (27643759/62500000)
  chi := (12369653/20000000)
  wE := (166918963/250000000)
  wS := (9/25)
  cE := (300774127/500000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (673475080163/1000000000000)
  cLam := (75753198909/125000000000)
  plane := (1/1)
  wRadius := (11506057/100000000)
  cRadius := (31092137/500000000)

theorem lowTIParameters39_valid : Valid lowTIParameters39 := by
  constructor
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · have h : √((((166918963/250000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (159637154163/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters39,ta_lam] at h ⊢
    linarith
  · have h : √((((300774127/500000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (12828216517/62500000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters39,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]
  · norm_num [lowTIParameters39]

theorem lowTISupply39 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters39 (959/2000) (12/25) := by
  refine ⟨lowTIParameters39_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum20W hn using 1 <;> norm_num [lowTIParameters39]
  · convert lowUniformNum20C hn using 1 <;> norm_num [lowTIParameters39]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry39W hn hθ).1 (by norm_num [lowTIParameters39])
      (by norm_num [lowTIParameters39]) (by norm_num [lowTIParameters39])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry39C hn hθ).1 (by norm_num [lowTIParameters39])
      (by norm_num [lowTIParameters39]) (by norm_num [lowTIParameters39])
  · intro θ hθ
    exact (lowGeometry39W hn hθ).2
  · intro θ hθ
    exact (lowGeometry39C hn hθ).2

noncomputable def lowTIParameters40 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (57556627/500000000)
  cRadius := (62216807/1000000000)

theorem lowTIParameters40_valid : Valid lowTIParameters40 := by
  constructor
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters40,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters40,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]
  · norm_num [lowTIParameters40]

theorem lowTISupply40 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters40 (12/25) (961/2000) := by
  refine ⟨lowTIParameters40_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters40]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters40]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry40W hn hθ).1 (by norm_num [lowTIParameters40])
      (by norm_num [lowTIParameters40]) (by norm_num [lowTIParameters40])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry40C hn hθ).1 (by norm_num [lowTIParameters40])
      (by norm_num [lowTIParameters40]) (by norm_num [lowTIParameters40])
  · intro θ hθ
    exact (lowGeometry40W hn hθ).2
  · intro θ hθ
    exact (lowGeometry40C hn hθ).2

noncomputable def lowTIParameters41 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115165871/1000000000)
  cRadius := (15562327/250000000)

theorem lowTIParameters41_valid : Valid lowTIParameters41 := by
  constructor
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters41,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters41,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]
  · norm_num [lowTIParameters41]

theorem lowTISupply41 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters41 (961/2000) (481/1000) := by
  refine ⟨lowTIParameters41_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters41]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters41]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry41W hn hθ).1 (by norm_num [lowTIParameters41])
      (by norm_num [lowTIParameters41]) (by norm_num [lowTIParameters41])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry41C hn hθ).1 (by norm_num [lowTIParameters41])
      (by norm_num [lowTIParameters41]) (by norm_num [lowTIParameters41])
  · intro θ hθ
    exact (lowGeometry41W hn hθ).2
  · intro θ hθ
    exact (lowGeometry41C hn hθ).2

noncomputable def lowTIParameters42 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115218421/1000000000)
  cRadius := (62281777/1000000000)

theorem lowTIParameters42_valid : Valid lowTIParameters42 := by
  constructor
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters42,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters42,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]
  · norm_num [lowTIParameters42]

theorem lowTISupply42 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters42 (481/1000) (963/2000) := by
  refine ⟨lowTIParameters42_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters42]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters42]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry42W hn hθ).1 (by norm_num [lowTIParameters42])
      (by norm_num [lowTIParameters42]) (by norm_num [lowTIParameters42])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry42C hn hθ).1 (by norm_num [lowTIParameters42])
      (by norm_num [lowTIParameters42]) (by norm_num [lowTIParameters42])
  · intro θ hθ
    exact (lowGeometry42W hn hθ).2
  · intro θ hθ
    exact (lowGeometry42C hn hθ).2

noncomputable def lowTIParameters43 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115270903/1000000000)
  cRadius := (62314213/1000000000)

theorem lowTIParameters43_valid : Valid lowTIParameters43 := by
  constructor
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters43,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters43,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]
  · norm_num [lowTIParameters43]

theorem lowTISupply43 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters43 (963/2000) (241/500) := by
  refine ⟨lowTIParameters43_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters43]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters43]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry43W hn hθ).1 (by norm_num [lowTIParameters43])
      (by norm_num [lowTIParameters43]) (by norm_num [lowTIParameters43])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry43C hn hθ).1 (by norm_num [lowTIParameters43])
      (by norm_num [lowTIParameters43]) (by norm_num [lowTIParameters43])
  · intro θ hθ
    exact (lowGeometry43W hn hθ).2
  · intro θ hθ
    exact (lowGeometry43C hn hθ).2

noncomputable def lowTIParameters44 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115323319/1000000000)
  cRadius := (31173309/500000000)

theorem lowTIParameters44_valid : Valid lowTIParameters44 := by
  constructor
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters44,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters44,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]
  · norm_num [lowTIParameters44]

theorem lowTISupply44 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters44 (241/500) (193/400) := by
  refine ⟨lowTIParameters44_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters44]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters44]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry44W hn hθ).1 (by norm_num [lowTIParameters44])
      (by norm_num [lowTIParameters44]) (by norm_num [lowTIParameters44])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry44C hn hθ).1 (by norm_num [lowTIParameters44])
      (by norm_num [lowTIParameters44]) (by norm_num [lowTIParameters44])
  · intro θ hθ
    exact (lowGeometry44W hn hθ).2
  · intro θ hθ
    exact (lowGeometry44C hn hθ).2

noncomputable def lowTIParameters45 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (115375667/1000000000)
  cRadius := (6237899/100000000)

theorem lowTIParameters45_valid : Valid lowTIParameters45 := by
  constructor
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters45,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters45,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]
  · norm_num [lowTIParameters45]

theorem lowTISupply45 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters45 (193/400) (483/1000) := by
  refine ⟨lowTIParameters45_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters45]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters45]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry45W hn hθ).1 (by norm_num [lowTIParameters45])
      (by norm_num [lowTIParameters45]) (by norm_num [lowTIParameters45])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry45C hn hθ).1 (by norm_num [lowTIParameters45])
      (by norm_num [lowTIParameters45]) (by norm_num [lowTIParameters45])
  · intro θ hθ
    exact (lowGeometry45W hn hθ).2
  · intro θ hθ
    exact (lowGeometry45C hn hθ).2

noncomputable def lowTIParameters46 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (28856987/250000000)
  cRadius := (6241133/100000000)

theorem lowTIParameters46_valid : Valid lowTIParameters46 := by
  constructor
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters46,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters46,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]
  · norm_num [lowTIParameters46]

theorem lowTISupply46 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters46 (483/1000) (967/2000) := by
  refine ⟨lowTIParameters46_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters46]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters46]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry46W hn hθ).1 (by norm_num [lowTIParameters46])
      (by norm_num [lowTIParameters46]) (by norm_num [lowTIParameters46])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry46C hn hθ).1 (by norm_num [lowTIParameters46])
      (by norm_num [lowTIParameters46]) (by norm_num [lowTIParameters46])
  · intro θ hθ
    exact (lowGeometry46W hn hθ).2
  · intro θ hθ
    exact (lowGeometry46C hn hθ).2

noncomputable def lowTIParameters47 : Parameters where
  wlo := (178385151/500000000)
  whi := (716969799/1000000000)
  clo := (432260647/1000000000)
  chi := (38043751/62500000)
  wE := (330706501/500000000)
  wS := (9/25)
  cE := (596175073/1000000000)
  cS := (1/5)
  o := (42636997/1000000000)
  wLam := (333664110151/500000000000)
  cLam := (600711783889/1000000000000)
  plane := (1/1)
  wRadius := (57740081/500000000)
  cRadius := (62443637/1000000000)

theorem lowTIParameters47_valid : Valid lowTIParameters47 := by
  constructor
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · have h : √((((330706501/500000000) - (9/25)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (78310859651/500000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters47,ta_lam] at h ⊢
    linarith
  · have h : √((((596175073/1000000000) - (1/5)) / 2) ^ 2 + (42636997/1000000000) ^ 2 : ℝ) ≤ (202624247389/1000000000000) :=
      sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
    norm_num only [lowTIParameters47,ta_lam] at h ⊢
    linarith
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]
  · norm_num [lowTIParameters47]

theorem lowTISupply47 {n : ℕ} (hn : 8000 ≤ n) :
    LowTISupply n lowTIParameters47 (967/2000) (121/250) := by
  refine ⟨lowTIParameters47_valid, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert lowUniformNum40W hn using 1 <;> norm_num [lowTIParameters47]
  · convert lowUniformNum40C hn using 1 <;> norm_num [lowTIParameters47]
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry47W hn hθ).1 (by norm_num [lowTIParameters47])
      (by norm_num [lowTIParameters47]) (by norm_num [lowTIParameters47])
  · intro θ hθ
    exact overlapGuard_widen (lowGeometry47C hn hθ).1 (by norm_num [lowTIParameters47])
      (by norm_num [lowTIParameters47]) (by norm_num [lowTIParameters47])
  · intro θ hθ
    exact (lowGeometry47W hn hθ).2
  · intro θ hθ
    exact (lowGeometry47C hn hθ).2

end BstLean.BlueprintLow
