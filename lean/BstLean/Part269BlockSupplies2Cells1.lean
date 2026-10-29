import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1
import BstLean.Part264bUniformTI
import BstLean.Part264Covariance
namespace BstLean.Part269.BG2
open Real Set BstLean.Part263 BstLean.Part264 BstLean.Part264b BstLean.Part255
theorem geometry32 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨22,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 32 ≤ θ ∧ θ ≤ noiseNode G.top 33 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (249020276642974602314823/500000000000000000000000) (499373634426249844843191/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry32W hn hc
  have hk := wideBlock1Geometry32C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨22,by decide⟩) (cellLower G (sourceIndex ⟨22,by decide⟩))
      (cellUpper G (sourceIndex ⟨22,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum32W (by have := hn.1; omega),
    uniformNum32C (by have := hn.1; omega),
    fun _ hθ => (geometry32 hn G ht hθ).1,
    fun _ hθ => (geometry32 hn G ht hθ).2.1⟩

theorem geometry33 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨23,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 33 ≤ θ ∧ θ ≤ noiseNode G.top 34 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (499229320576135117274323/1000000000000000000000000) (1564271171448152909533/3125000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry33W hn hc
  have hk := wideBlock1Geometry33C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨23,by decide⟩) (cellLower G (sourceIndex ⟨23,by decide⟩))
      (cellUpper G (sourceIndex ⟨23,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum33W (by have := hn.1; omega),
    uniformNum33C (by have := hn.1; omega),
    fun _ hθ => (geometry33 hn G ht hθ).1,
    fun _ hθ => (geometry33 hn G ht hθ).2.1⟩

theorem geometry34 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨24,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 34 ≤ θ ∧ θ ≤ noiseNode G.top 35 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (500418087866321029918999/1000000000000000000000000) (50175991530056801725793/100000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry34W hn hc
  have hk := wideBlock1Geometry34C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨24,by decide⟩) (cellLower G (sourceIndex ⟨24,by decide⟩))
      (cellUpper G (sourceIndex ⟨24,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum34W (by have := hn.1; omega),
    uniformNum34C (by have := hn.1; omega),
    fun _ hθ => (geometry34 hn G ht hθ).1,
    fun _ hθ => (geometry34 hn G ht hθ).2.1⟩

theorem geometry35 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨25,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 35 ≤ θ ∧ θ ≤ noiseNode G.top 36 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (125401713789126735640919/250000000000000000000000) (502953055737727103465299/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry35W hn hc
  have hk := wideBlock1Geometry35C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨25,by decide⟩) (cellLower G (sourceIndex ⟨25,by decide⟩))
      (cellUpper G (sourceIndex ⟨25,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum35W (by have := hn.1; omega),
    uniformNum35C (by have := hn.1; omega),
    fun _ hθ => (geometry35 hn G ht hθ).1,
    fun _ hθ => (geometry35 hn G ht hθ).2.1⟩

theorem geometry36 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨26,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 36 ≤ θ ∧ θ ≤ noiseNode G.top 37 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (15712363201459151725261/31250000000000000000000) (126036549043721547418167/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry36W hn hc
  have hk := wideBlock1Geometry36C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨26,by decide⟩) (cellLower G (sourceIndex ⟨26,by decide⟩))
      (cellUpper G (sourceIndex ⟨26,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum36W (by have := hn.1; omega),
    uniformNum36C (by have := hn.1; omega),
    fun _ hθ => (geometry36 hn G ht hθ).1,
    fun _ hθ => (geometry36 hn G ht hθ).2.1⟩

theorem geometry37 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨27,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 37 ≤ θ ∧ θ ≤ noiseNode G.top 38 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (503984389736878767853029/1000000000000000000000000) (252669668306022637940019/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry37W hn hc
  have hk := wideBlock1Geometry37C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨27,by decide⟩) (cellLower G (sourceIndex ⟨27,by decide⟩))
      (cellUpper G (sourceIndex ⟨27,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum37W (by have := hn.1; omega),
    uniformNum37C (by have := hn.1; omega),
    fun _ hθ => (geometry37 hn G ht hθ).1,
    fun _ hθ => (geometry37 hn G ht hθ).2.1⟩

theorem geometry38 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨28,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 38 ≤ θ ∧ θ ≤ noiseNode G.top 39 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (101034631405412936099541/200000000000000000000000) (506532477049204362087407/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry38W hn hc
  have hk := wideBlock1Geometry38C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨28,by decide⟩) (cellLower G (sourceIndex ⟨28,by decide⟩))
      (cellUpper G (sourceIndex ⟨28,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum38W (by have := hn.1; omega),
    uniformNum38C (by have := hn.1; omega),
    fun _ hθ => (geometry38 hn G ht hθ).1,
    fun _ hθ => (geometry38 hn G ht hθ).2.1⟩

theorem geometry39 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨29,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 39 ≤ θ ∧ θ ≤ noiseNode G.top 40 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (253180962158625296571191/500000000000000000000000) (507725617486363448294777/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry39W hn hc
  have hk := wideBlock1Geometry39C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨29,by decide⟩) (cellLower G (sourceIndex ⟨29,by decide⟩))
      (cellUpper G (sourceIndex ⟨29,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum39W (by have := hn.1; omega),
    uniformNum39C (by have := hn.1; omega),
    fun _ hθ => (geometry39 hn G ht hθ).1,
    fun _ hθ => (geometry39 hn G ht hθ).2.1⟩

theorem geometry40 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨30,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 40 ≤ θ ∧ θ ≤ noiseNode G.top 41 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (253775345803718252893529/500000000000000000000000) (254459378961761267251073/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry40W hn hc
  have hk := wideBlock1Geometry40C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨30,by decide⟩) (cellLower G (sourceIndex ⟨30,by decide⟩))
      (cellUpper G (sourceIndex ⟨30,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum40W (by have := hn.1; omega),
    uniformNum40C (by have := hn.1; omega),
    fun _ hθ => (geometry40 hn G ht hθ).1,
    fun _ hθ => (geometry40 hn G ht hθ).2.1⟩

theorem geometry41 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨31,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 41 ≤ θ ∧ θ ≤ noiseNode G.top 42 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (101747891779524483686347/200000000000000000000000) (102022379672136324141903/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry41W hn hc
  have hk := wideBlock1Geometry41C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨31,by decide⟩) (cellLower G (sourceIndex ⟨31,by decide⟩))
      (cellUpper G (sourceIndex ⟨31,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum41W (by have := hn.1; omega),
    uniformNum41C (by have := hn.1; omega),
    fun _ hθ => (geometry41 hn G ht hθ).1,
    fun _ hθ => (geometry41 hn G ht hθ).2.1⟩

theorem geometry42 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨32,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 42 ≤ θ ∧ θ ≤ noiseNode G.top 43 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (509928226187808331076411/1000000000000000000000000) (102261007759568141383377/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry42W hn hc
  have hk := wideBlock1Geometry42C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨32,by decide⟩) (cellLower G (sourceIndex ⟨32,by decide⟩))
      (cellUpper G (sourceIndex ⟨32,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum42W (by have := hn.1; omega),
    uniformNum42C (by have := hn.1; omega),
    fun _ hθ => (geometry42 hn G ht hθ).1,
    fun _ hθ => (geometry42 hn G ht hθ).2.1⟩

theorem geometry43 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨33,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 43 ≤ θ ∧ θ ≤ noiseNode G.top 44 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (3993101511546830029071/7812500000000000000000) (256249089617499896562127/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry43W hn hc
  have hk := wideBlock1Geometry43C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨33,by decide⟩) (cellLower G (sourceIndex ⟨33,by decide⟩))
      (cellUpper G (sourceIndex ⟨33,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum43W (by have := hn.1; omega),
    uniformNum43C (by have := hn.1; omega),
    fun _ hθ => (geometry43 hn G ht hθ).1,
    fun _ hθ => (geometry43 hn G ht hθ).2.1⟩

theorem geometry44 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨34,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 44 ≤ θ ∧ θ ≤ noiseNode G.top 45 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (128076440192045039091441/250000000000000000000000) (64211414959019859916453/125000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry44W hn hc
  have hk := wideBlock1Geometry44C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨34,by decide⟩) (cellLower G (sourceIndex ⟨34,by decide⟩))
      (cellUpper G (sourceIndex ⟨34,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum44W (by have := hn.1; omega),
    uniformNum44C (by have := hn.1; omega),
    fun _ hθ => (geometry44 hn G ht hθ).1,
    fun _ hθ => (geometry44 hn G ht hθ).2.1⟩

theorem geometry45 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨35,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 45 ≤ θ ∧ θ ≤ noiseNode G.top 46 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (12837363201459151725261/25000000000000000000000) (514884460109317965538993/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry45W hn hc
  have hk := wideBlock1Geometry45C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨35,by decide⟩) (cellLower G (sourceIndex ⟨35,by decide⟩))
      (cellUpper G (sourceIndex ⟨35,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum45W (by have := hn.1; omega),
    uniformNum45C (by have := hn.1; omega),
    fun _ hθ => (geometry45 hn G ht hθ).1,
    fun _ hθ => (geometry45 hn G ht hθ).2.1⟩

theorem geometry46 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨36,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 46 ≤ θ ∧ θ ≤ noiseNode G.top 47 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (514683295348551981655117/1000000000000000000000000) (258038800273238525873181/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry46W hn hc
  have hk := wideBlock1Geometry46C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨36,by decide⟩) (cellLower G (sourceIndex ⟨36,by decide⟩))
      (cellUpper G (sourceIndex ⟨36,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum46W (by have := hn.1; omega),
    uniformNum46C (by have := hn.1; omega),
    fun _ hθ => (geometry46 hn G ht hθ).1,
    fun _ hθ => (geometry46 hn G ht hθ).2.1⟩

theorem geometry47 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨37,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 47 ≤ θ ∧ θ ≤ noiseNode G.top 48 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (515872062638737894299793/1000000000000000000000000) (129317685245909034488433/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry47W hn hc
  have hk := wideBlock1Geometry47C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨37,by decide⟩) (cellLower G (sourceIndex ⟨37,by decide⟩))
      (cellUpper G (sourceIndex ⟨37,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum47W (by have := hn.1; omega),
    uniformNum47C (by have := hn.1; omega),
    fun _ hθ => (geometry47 hn G ht hθ).1,
    fun _ hθ => (geometry47 hn G ht hθ).2.1⟩

theorem geometry48 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨38,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 48 ≤ θ ∧ θ ≤ noiseNode G.top 49 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (51706082992892380694447/100000000000000000000000) (518463881420795224161101/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry48W hn hc
  have hk := wideBlock1Geometry48C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨38,by decide⟩) (cellLower G (sourceIndex ⟨38,by decide⟩))
      (cellUpper G (sourceIndex ⟨38,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum48W (by have := hn.1; omega),
    uniformNum48C (by have := hn.1; omega),
    fun _ hθ => (geometry48 hn G ht hθ).1,
    fun _ hθ => (geometry48 hn G ht hθ).2.1⟩

theorem geometry49 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨39,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 49 ≤ θ ∧ θ ≤ noiseNode G.top 50 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (259124798609554859794573/500000000000000000000000) (519657021857954310368471/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry49W hn hc
  have hk := wideBlock1Geometry49C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨39,by decide⟩) (cellLower G (sourceIndex ⟨39,by decide⟩))
      (cellUpper G (sourceIndex ⟨39,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum49W (by have := hn.1; omega),
    uniformNum49C (by have := hn.1; omega),
    fun _ hθ => (geometry49 hn G ht hθ).1,
    fun _ hθ => (geometry49 hn G ht hθ).2.1⟩

theorem geometry50 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨40,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 50 ≤ θ ∧ θ ≤ noiseNode G.top 51 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (519438364509295632233823/1000000000000000000000000) (3255313514344458728599/6250000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry50W hn hc
  have hk := wideBlock1Geometry50C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨40,by decide⟩) (cellLower G (sourceIndex ⟨40,by decide⟩))
      (cellUpper G (sourceIndex ⟨40,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum50W (by have := hn.1; omega),
    uniformNum50C (by have := hn.1; omega),
    fun _ hθ => (geometry50 hn G ht hθ).1,
    fun _ hθ => (geometry50 hn G ht hθ).2.1⟩

theorem geometry51 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨41,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 51 ≤ θ ∧ θ ≤ noiseNode G.top 52 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (520627131799481544878499/1000000000000000000000000) (522043302732272482783209/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry51W hn hc
  have hk := wideBlock1Geometry51C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨41,by decide⟩) (cellLower G (sourceIndex ⟨41,by decide⟩))
      (cellUpper G (sourceIndex ⟨41,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum51W (by have := hn.1; omega),
    uniformNum51C (by have := hn.1; omega),
    fun _ hθ => (geometry51 hn G ht hθ).1,
    fun _ hθ => (geometry51 hn G ht hθ).2.1⟩

theorem geometry52 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨42,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 52 ≤ θ ∧ θ ≤ noiseNode G.top 53 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (65226987386208432190397/125000000000000000000000) (523236443169431568990579/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry52W hn hc
  have hk := wideBlock1Geometry52C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨42,by decide⟩) (cellLower G (sourceIndex ⟨42,by decide⟩))
      (cellUpper G (sourceIndex ⟨42,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum52W (by have := hn.1; omega),
    uniformNum52C (by have := hn.1; omega),
    fun _ hθ => (geometry52 hn G ht hθ).1,
    fun _ hθ => (geometry52 hn G ht hθ).2.1⟩

end BstLean.Part269.BG2
