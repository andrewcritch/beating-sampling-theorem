import BstLean.Part269Geometry0_0
import BstLean.Part269Geometry0_1
import BstLean.Part264bUniformTI
import BstLean.Part264Covariance
namespace BstLean.Part269.BG0
open Real Set BstLean.Part263 BstLean.Part264 BstLean.Part264b BstLean.Part255
theorem geometry32 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨22,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 32 ≤ θ ∧ θ ≤ noiseNode G.top 33 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (99665685541475044605589/200000000000000000000000) (499535024825144757735067/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry32W hn hc
  have hk := block0Geometry32C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨22,by decide⟩) (cellLower G (sourceIndex ⟨22,by decide⟩))
      (cellUpper G (sourceIndex ⟨22,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum32W (by have := hn.1; omega),
    uniformNum32C (by have := hn.1; omega),
    fun _ hθ => (geometry32 hn G ht hθ).1,
    fun _ hθ => (geometry32 hn G ht hθ).2.1⟩

theorem geometry33 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨23,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 33 ≤ θ ∧ θ ≤ noiseNode G.top 34 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (31220386942076918671723/62500000000000000000000) (500733055880452174636129/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry33W hn hc
  have hk := block0Geometry33C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨23,by decide⟩) (cellLower G (sourceIndex ⟨23,by decide⟩))
      (cellUpper G (sourceIndex ⟨23,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum33W (by have := hn.1; omega),
    uniformNum33C (by have := hn.1; omega),
    fun _ hθ => (geometry33 hn G ht hθ).1,
    fun _ hθ => (geometry33 hn G ht hθ).2.1⟩

theorem geometry34 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨24,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 34 ≤ θ ∧ θ ≤ noiseNode G.top 35 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (500723954439086174467191/1000000000000000000000000) (62741385866969948942149/125000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry34W hn hc
  have hk := block0Geometry34C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨24,by decide⟩) (cellLower G (sourceIndex ⟨24,by decide⟩))
      (cellUpper G (sourceIndex ⟨24,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum34W (by have := hn.1; omega),
    uniformNum34C (by have := hn.1; omega),
    fun _ hθ => (geometry34 hn G ht hθ).1,
    fun _ hθ => (geometry34 hn G ht hθ).2.1⟩

theorem geometry35 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨25,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 35 ≤ θ ∧ θ ≤ noiseNode G.top 36 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (250960858902470825093407/500000000000000000000000) (100625823598213401687651/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry35W hn hc
  have hk := block0Geometry35C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨25,by decide⟩) (cellLower G (sourceIndex ⟨25,by decide⟩))
      (cellUpper G (sourceIndex ⟨25,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum35W (by have := hn.1; omega),
    uniformNum35C (by have := hn.1; omega),
    fun _ hθ => (geometry35 hn G ht hθ).1,
    fun _ hθ => (geometry35 hn G ht hθ).2.1⟩

theorem geometry36 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨26,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 36 ≤ θ ∧ θ ≤ noiseNode G.top 37 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (251559740585398562953219/500000000000000000000000) (504327149046374425339317/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry36W hn hc
  have hk := block0Geometry36C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨26,by decide⟩) (cellLower G (sourceIndex ⟨26,by decide⟩))
      (cellUpper G (sourceIndex ⟨26,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum36W (by have := hn.1; omega),
    uniformNum36C (by have := hn.1; omega),
    fun _ hθ => (geometry36 hn G ht hθ).1,
    fun _ hθ => (geometry36 hn G ht hθ).2.1⟩

theorem geometry37 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨27,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 37 ≤ θ ∧ θ ≤ noiseNode G.top 38 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (504317244536652601626061/1000000000000000000000000) (25276259005084092112019/50000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry37W hn hc
  have hk := block0Geometry37C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨27,by decide⟩) (cellLower G (sourceIndex ⟨27,by decide⟩))
      (cellUpper G (sourceIndex ⟨27,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum37W (by have := hn.1; omega),
    uniformNum37C (by have := hn.1; omega),
    fun _ hθ => (geometry37 hn G ht hθ).1,
    fun _ hθ => (geometry37 hn G ht hθ).2.1⟩

theorem geometry38 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨28,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 38 ≤ θ ∧ θ ≤ noiseNode G.top 39 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (126378751975627019336421/250000000000000000000000) (506723211156989259141443/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry38W hn hc
  have hk := block0Geometry38C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨28,by decide⟩) (cellLower G (sourceIndex ⟨28,by decide⟩))
      (cellUpper G (sourceIndex ⟨28,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum38W (by have := hn.1; omega),
    uniformNum38C (by have := hn.1; omega),
    fun _ hθ => (geometry38 hn G ht hθ).1,
    fun _ hθ => (geometry38 hn G ht hθ).2.1⟩

theorem geometry39 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨29,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 39 ≤ θ ∧ θ ≤ noiseNode G.top 40 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (126678192817090888266327/250000000000000000000000) (101584248442459335208501/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry39W hn hc
  have hk := block0Geometry39C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨29,by decide⟩) (cellLower G (sourceIndex ⟨29,by decide⟩))
      (cellUpper G (sourceIndex ⟨29,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum39W (by have := hn.1; omega),
    uniformNum39C (by have := hn.1; omega),
    fun _ hθ => (geometry39 hn G ht hθ).1,
    fun _ hθ => (geometry39 hn G ht hθ).2.1⟩

theorem geometry40 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨30,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 40 ≤ θ ∧ θ ≤ noiseNode G.top 41 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (507910534634219028784931/1000000000000000000000000) (31819954579225255808973/62500000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry40W hn hc
  have hk := block0Geometry40C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨30,by decide⟩) (cellLower G (sourceIndex ⟨30,by decide⟩))
      (cellUpper G (sourceIndex ⟨30,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum40W (by have := hn.1; omega),
    uniformNum40C (by have := hn.1; omega),
    fun _ hθ => (geometry40 hn G ht hθ).1,
    fun _ hθ => (geometry40 hn G ht hθ).2.1⟩

theorem geometry41 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨31,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 41 ≤ θ ∧ θ ≤ noiseNode G.top 42 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (254554149000037252252277/500000000000000000000000) (51031730432291150984463/100000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry41W hn hc
  have hk := block0Geometry41C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨31,by decide⟩) (cellLower G (sourceIndex ⟨31,by decide⟩))
      (cellUpper G (sourceIndex ⟨31,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum41W (by have := hn.1; omega),
    uniformNum41C (by have := hn.1; omega),
    fun _ hθ => (geometry41 hn G ht hθ).1,
    fun _ hθ => (geometry41 hn G ht hθ).2.1⟩

theorem geometry42 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨32,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 42 ≤ θ ∧ θ ≤ noiseNode G.top 43 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (510306061365929980224177/1000000000000000000000000) (511515335378218926745693/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry42W hn hc
  have hk := block0Geometry42C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨32,by decide⟩) (cellLower G (sourceIndex ⟨32,by decide⟩))
      (cellUpper G (sourceIndex ⟨32,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum42W (by have := hn.1; omega),
    uniformNum42C (by have := hn.1; omega),
    fun _ hθ => (geometry42 hn G ht hθ).1,
    fun _ hθ => (geometry42 hn G ht hθ).2.1⟩

theorem geometry43 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨33,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 43 ≤ θ ∧ θ ≤ noiseNode G.top 44 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (511503824731785455943801/1000000000000000000000000) (128178341608381585911689/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry43W hn hc
  have hk := block0Geometry43C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨33,by decide⟩) (cellLower G (sourceIndex ⟨33,by decide⟩))
      (cellUpper G (sourceIndex ⟨33,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum43W (by have := hn.1; omega),
    uniformNum43C (by have := hn.1; omega),
    fun _ hθ => (geometry43 hn G ht hθ).1,
    fun _ hθ => (geometry43 hn G ht hθ).2.1⟩

theorem geometry44 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨34,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 44 ≤ θ ∧ θ ≤ noiseNode G.top 45 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (8010962314025639557241/15625000000000000000000) (256955698744416880273909/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry44W hn hc
  have hk := block0Geometry44C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨34,by decide⟩) (cellLower G (sourceIndex ⟨34,by decide⟩))
      (cellUpper G (sourceIndex ⟨34,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum44W (by have := hn.1; omega),
    uniformNum44C (by have := hn.1; omega),
    fun _ hθ => (geometry44 hn G ht hθ).1,
    fun _ hθ => (geometry44 hn G ht hθ).2.1⟩

theorem geometry45 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨35,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 45 ≤ θ ∧ θ ≤ noiseNode G.top 46 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (513899351463496407383047/1000000000000000000000000) (515109428544141177448881/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry45W hn hc
  have hk := block0Geometry45C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨35,by decide⟩) (cellLower G (sourceIndex ⟨35,by decide⟩))
      (cellUpper G (sourceIndex ⟨35,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum45W (by have := hn.1; omega),
    uniformNum45C (by have := hn.1; omega),
    fun _ hθ => (geometry45 hn G ht hθ).1,
    fun _ hθ => (geometry45 hn G ht hθ).2.1⟩

theorem geometry46 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨36,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 46 ≤ θ ∧ θ ≤ noiseNode G.top 47 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (515097114829351883102671/1000000000000000000000000) (516307459599448594349943/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry46W hn hc
  have hk := block0Geometry46C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨36,by decide⟩) (cellLower G (sourceIndex ⟨36,by decide⟩))
      (cellUpper G (sourceIndex ⟨36,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum46W (by have := hn.1; omega),
    uniformNum46C (by have := hn.1; omega),
    fun _ hθ => (geometry46 hn G ht hθ).1,
    fun _ hθ => (geometry46 hn G ht hθ).2.1⟩

theorem geometry47 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨37,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 47 ≤ θ ∧ θ ≤ noiseNode G.top 48 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (258147439097603679411147/500000000000000000000000) (258752745327378005625503/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry47W hn hc
  have hk := block0Geometry47C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨37,by decide⟩) (cellLower G (sourceIndex ⟨37,by decide⟩))
      (cellUpper G (sourceIndex ⟨37,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum47W (by have := hn.1; omega),
    uniformNum47C (by have := hn.1; omega),
    fun _ hθ => (geometry47 hn G ht hθ).1,
    fun _ hθ => (geometry47 hn G ht hθ).2.1⟩

theorem geometry48 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨38,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 48 ≤ θ ∧ θ ≤ noiseNode G.top 49 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (517492641561062834541917/1000000000000000000000000) (518703521710063428152069/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry48W hn hc
  have hk := block0Geometry48C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨38,by decide⟩) (cellLower G (sourceIndex ⟨38,by decide⟩))
      (cellUpper G (sourceIndex ⟨38,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum48W (by have := hn.1; omega),
    uniformNum48C (by have := hn.1; omega),
    fun _ hθ => (geometry48 hn G ht hθ).1,
    fun _ hθ => (geometry48 hn G ht hθ).2.1⟩

theorem geometry49 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨39,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 49 ≤ θ ∧ θ ≤ noiseNode G.top 50 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (25934520246345915513077/50000000000000000000000) (519901552765370845053131/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry49W hn hc
  have hk := block0Geometry49C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨39,by decide⟩) (cellLower G (sourceIndex ⟨39,by decide⟩))
      (cellUpper G (sourceIndex ⟨39,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum49W (by have := hn.1; omega),
    uniformNum49C (by have := hn.1; omega),
    fun _ hθ => (geometry49 hn G ht hθ).1,
    fun _ hθ => (geometry49 hn G ht hθ).2.1⟩

theorem geometry50 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨40,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 50 ≤ θ ∧ θ ≤ noiseNode G.top 51 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (129972042073193446495291/250000000000000000000000) (260549791910339130977097/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry50W hn hc
  have hk := block0Geometry50C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨40,by decide⟩) (cellLower G (sourceIndex ⟨40,by decide⟩))
      (cellUpper G (sourceIndex ⟨40,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum50W (by have := hn.1; omega),
    uniformNum50C (by have := hn.1; omega),
    fun _ hθ => (geometry50 hn G ht hθ).1,
    fun _ hθ => (geometry50 hn G ht hθ).2.1⟩

theorem geometry51 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨41,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 51 ≤ θ ∧ θ ≤ noiseNode G.top 52 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (521085931658629261700787/1000000000000000000000000) (522297614875985678855257/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry51W hn hc
  have hk := block0Geometry51C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨41,by decide⟩) (cellLower G (sourceIndex ⟨41,by decide⟩))
      (cellUpper G (sourceIndex ⟨41,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum51W (by have := hn.1; omega),
    uniformNum51C (by have := hn.1; omega),
    fun _ hθ => (geometry51 hn G ht hθ).1,
    fun _ hθ => (geometry51 hn G ht hθ).2.1⟩

theorem geometry52 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨42,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 52 ≤ θ ∧ θ ≤ noiseNode G.top 53 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (52228369502448473742041/100000000000000000000000) (523495645931293095756319/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := block0Geometry52W hn hc
  have hk := block0Geometry52C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 {n : ℕ} (hn : n ∈ Icc 12350 12374) (G : Grid) (ht : G.top ∈ Icc (531865801951328543177397/1000000000000000000000000) (531881863318445014063757/1000000000000000000000000)) :
    Supply n (parameters ⟨42,by decide⟩) (cellLower G (sourceIndex ⟨42,by decide⟩))
      (cellUpper G (sourceIndex ⟨42,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum52W (by have := hn.1; omega),
    uniformNum52C (by have := hn.1; omega),
    fun _ hθ => (geometry52 hn G ht hθ).1,
    fun _ hθ => (geometry52 hn G ht hθ).2.1⟩

end BstLean.Part269.BG0
