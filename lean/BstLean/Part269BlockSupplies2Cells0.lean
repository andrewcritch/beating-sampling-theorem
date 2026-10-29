import BstLean.Part269WideGeometry1_0
import BstLean.Part269WideGeometry1_1
import BstLean.Part264bUniformTI
import BstLean.Part264Covariance
namespace BstLean.Part269.BG2
open Real Set BstLean.Part263 BstLean.Part264 BstLean.Part264b BstLean.Part255
theorem geometry10 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨0,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 10 ≤ θ ∧ θ ≤ noiseNode G.top 11 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (117971918225464781611691/250000000000000000000000) (59140568101093743535133/125000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry10W hn hc
  have hk := wideBlock1Geometry10C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply10 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨0,by decide⟩) (cellLower G (sourceIndex ⟨0,by decide⟩))
      (cellUpper G (sourceIndex ⟨0,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum10W (by have := hn.1; omega),
    uniformNum10C (by have := hn.1; omega),
    fun _ hθ => (geometry10 hn G ht hθ).1,
    fun _ hθ => (geometry10 hn G ht hθ).2.1⟩

theorem geometry11 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨1,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 11 ≤ θ ∧ θ ≤ noiseNode G.top 12 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (473076440192045039091441/1000000000000000000000000) (474317685245909034488433/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry11W hn hc
  have hk := wideBlock1Geometry11C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply11 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨1,by decide⟩) (cellLower G (sourceIndex ⟨1,by decide⟩))
      (cellUpper G (sourceIndex ⟨1,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum11W (by have := hn.1; omega),
    uniformNum11C (by have := hn.1; omega),
    fun _ hθ => (geometry11 hn G ht hθ).1,
    fun _ hθ => (geometry11 hn G ht hθ).2.1⟩

theorem geometry12 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨2,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 12 ≤ θ ∧ θ ≤ noiseNode G.top 13 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (474265207482230951736117/1000000000000000000000000) (475510825683068120695803/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry12W hn hc
  have hk := wideBlock1Geometry12C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply12 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨2,by decide⟩) (cellLower G (sourceIndex ⟨2,by decide⟩))
      (cellUpper G (sourceIndex ⟨2,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum12W (by have := hn.1; omega),
    uniformNum12C (by have := hn.1; omega),
    fun _ hθ => (geometry12 hn G ht hθ).1,
    fun _ hθ => (geometry12 hn G ht hθ).2.1⟩

theorem geometry13 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨3,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 13 ≤ θ ∧ θ ≤ noiseNode G.top 14 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (237726987386208432190397/500000000000000000000000) (119175991530056801725793/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry13W hn hc
  have hk := wideBlock1Geometry13C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply13 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨3,by decide⟩) (cellLower G (sourceIndex ⟨3,by decide⟩))
      (cellUpper G (sourceIndex ⟨3,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum13W (by have := hn.1; omega),
    uniformNum13C (by have := hn.1; omega),
    fun _ hθ => (geometry13 hn G ht hθ).1,
    fun _ hθ => (geometry13 hn G ht hθ).2.1⟩

theorem geometry14 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨4,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 14 ≤ θ ∧ θ ≤ noiseNode G.top 15 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (47664274206260277702547/100000000000000000000000) (238948553278693146555271/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry14W hn hc
  have hk := wideBlock1Geometry14C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply14 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨4,by decide⟩) (cellLower G (sourceIndex ⟨4,by decide⟩))
      (cellUpper G (sourceIndex ⟨4,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum14W (by have := hn.1; omega),
    uniformNum14C (by have := hn.1; omega),
    fun _ hθ => (geometry14 hn G ht hθ).1,
    fun _ hθ => (geometry14 hn G ht hθ).2.1⟩

theorem geometry15 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨5,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 15 ≤ θ ∧ θ ≤ noiseNode G.top 16 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (238915754676394344835073/500000000000000000000000) (479090246994545379317911/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry15W hn hc
  have hk := wideBlock1Geometry15C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply15 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨5,by decide⟩) (cellLower G (sourceIndex ⟨5,by decide⟩))
      (cellUpper G (sourceIndex ⟨5,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum15W (by have := hn.1; omega),
    uniformNum15C (by have := hn.1; omega),
    fun _ hθ => (geometry15 hn G ht hθ).1,
    fun _ hθ => (geometry15 hn G ht hθ).2.1⟩

theorem geometry16 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨6,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 16 ≤ θ ∧ θ ≤ noiseNode G.top 17 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (479020276642974602314823/1000000000000000000000000) (3001771171448152909533/6250000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry16W hn hc
  have hk := wideBlock1Geometry16C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply16 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨6,by decide⟩) (cellLower G (sourceIndex ⟨6,by decide⟩))
      (cellUpper G (sourceIndex ⟨6,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum16W (by have := hn.1; omega),
    uniformNum16C (by have := hn.1; omega),
    fun _ hθ => (geometry16 hn G ht hθ).1,
    fun _ hθ => (geometry16 hn G ht hθ).2.1⟩

theorem geometry17 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨7,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 17 ≤ θ ∧ θ ≤ noiseNode G.top 18 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (480209043933160514959499/1000000000000000000000000) (9629530557377271034653/20000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry17W hn hc
  have hk := wideBlock1Geometry17C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply17 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨7,by decide⟩) (cellLower G (sourceIndex ⟨7,by decide⟩))
      (cellUpper G (sourceIndex ⟨7,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum17W (by have := hn.1; omega),
    uniformNum17C (by have := hn.1; omega),
    fun _ hθ => (geometry17 hn G ht hθ).1,
    fun _ hθ => (geometry17 hn G ht hθ).2.1⟩

theorem geometry18 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨8,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 18 ≤ θ ∧ θ ≤ noiseNode G.top 19 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (30087363201459151725261/62500000000000000000000) (482669668306022637940019/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry18W hn hc
  have hk := wideBlock1Geometry18C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply18 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨8,by decide⟩) (cellLower G (sourceIndex ⟨8,by decide⟩))
      (cellUpper G (sourceIndex ⟨8,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum18W (by have := hn.1; omega),
    uniformNum18C (by have := hn.1; omega),
    fun _ hθ => (geometry18 hn G ht hθ).1,
    fun _ hθ => (geometry18 hn G ht hθ).2.1⟩

theorem geometry19 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨9,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 19 ≤ θ ∧ θ ≤ noiseNode G.top 20 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (120646644628383085062213/250000000000000000000000) (483862808743181724147389/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry19W hn hc
  have hk := wideBlock1Geometry19C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply19 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨9,by decide⟩) (cellLower G (sourceIndex ⟨9,by decide⟩))
      (cellUpper G (sourceIndex ⟨9,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum19W (by have := hn.1; omega),
    uniformNum19C (by have := hn.1; omega),
    fun _ hθ => (geometry19 hn G ht hθ).1,
    fun _ hθ => (geometry19 hn G ht hθ).2.1⟩

theorem geometry20 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨10,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 20 ≤ θ ∧ θ ≤ noiseNode G.top 21 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (483775345803718252893529/1000000000000000000000000) (242527974590170405177379/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry20W hn hc
  have hk := wideBlock1Geometry20C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply20 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨10,by decide⟩) (cellLower G (sourceIndex ⟨10,by decide⟩))
      (cellUpper G (sourceIndex ⟨10,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum20W (by have := hn.1; omega),
    uniformNum20C (by have := hn.1; omega),
    fun _ hθ => (geometry20 hn G ht hθ).1,
    fun _ hθ => (geometry20 hn G ht hθ).2.1⟩

theorem geometry21 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨11,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 21 ≤ θ ∧ θ ≤ noiseNode G.top 22 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (96992822618780833107641/200000000000000000000000) (486249089617499896562127/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry21W hn hc
  have hk := wideBlock1Geometry21C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply21 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨11,by decide⟩) (cellLower G (sourceIndex ⟨11,by decide⟩))
      (cellUpper G (sourceIndex ⟨11,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum21W (by have := hn.1; omega),
    uniformNum21C (by have := hn.1; omega),
    fun _ hθ => (geometry21 hn G ht hθ).1,
    fun _ hθ => (geometry21 hn G ht hθ).2.1⟩

theorem geometry22 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨12,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 22 ≤ θ ∧ θ ≤ noiseNode G.top 23 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (243076440192045039091441/500000000000000000000000) (487442230054658982769497/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry22W hn hc
  have hk := wideBlock1Geometry22C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply22 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨12,by decide⟩) (cellLower G (sourceIndex ⟨12,by decide⟩))
      (cellUpper G (sourceIndex ⟨12,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum22W (by have := hn.1; omega),
    uniformNum22C (by have := hn.1; omega),
    fun _ hθ => (geometry22 hn G ht hθ).1,
    fun _ hθ => (geometry22 hn G ht hθ).2.1⟩

theorem geometry23 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨13,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 23 ≤ θ ∧ θ ≤ noiseNode G.top 24 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (243670823837137995413779/500000000000000000000000) (244317685245909034488433/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry23W hn hc
  have hk := wideBlock1Geometry23C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply23 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨13,by decide⟩) (cellLower G (sourceIndex ⟨13,by decide⟩))
      (cellUpper G (sourceIndex ⟨13,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum23W (by have := hn.1; omega),
    uniformNum23C (by have := hn.1; omega),
    fun _ hθ => (geometry23 hn G ht hθ).1,
    fun _ hθ => (geometry23 hn G ht hθ).2.1⟩

theorem geometry24 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨14,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 24 ≤ θ ∧ θ ≤ noiseNode G.top 25 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (97706082992892380694447/200000000000000000000000) (122457127732244288796059/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry24W hn hc
  have hk := wideBlock1Geometry24C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply24 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨14,by decide⟩) (cellLower G (sourceIndex ⟨14,by decide⟩))
      (cellUpper G (sourceIndex ⟨14,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum24W (by have := hn.1; omega),
    uniformNum24C (by have := hn.1; omega),
    fun _ hθ => (geometry24 hn G ht hθ).1,
    fun _ hθ => (geometry24 hn G ht hθ).2.1⟩

theorem geometry25 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨15,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 25 ≤ θ ∧ θ ≤ noiseNode G.top 26 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (489719182254647816116911/1000000000000000000000000) (98204330273227248278321/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry25W hn hc
  have hk := wideBlock1Geometry25C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply25 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨15,by decide⟩) (cellLower G (sourceIndex ⟨15,by decide⟩))
      (cellUpper G (sourceIndex ⟨15,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum25W (by have := hn.1; omega),
    uniformNum25C (by have := hn.1; omega),
    fun _ hθ => (geometry25 hn G ht hθ).1,
    fun _ hθ => (geometry25 hn G ht hθ).2.1⟩

theorem geometry26 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨16,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 26 ≤ θ ∧ θ ≤ noiseNode G.top 27 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (122726987386208432190397/250000000000000000000000) (246107395901647663799487/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry26W hn hc
  have hk := wideBlock1Geometry26C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply26 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨16,by decide⟩) (cellLower G (sourceIndex ⟨16,by decide⟩))
      (cellUpper G (sourceIndex ⟨16,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum26W (by have := hn.1; omega),
    uniformNum26C (by have := hn.1; omega),
    fun _ hθ => (geometry26 hn G ht hθ).1,
    fun _ hθ => (geometry26 hn G ht hθ).2.1⟩

theorem geometry27 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨17,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 27 ≤ θ ∧ θ ≤ noiseNode G.top 28 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (61512089604377455175783/125000000000000000000000) (61675991530056801725793/125000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry27W hn hc
  have hk := wideBlock1Geometry27C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply27 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨17,by decide⟩) (cellLower G (sourceIndex ⟨17,by decide⟩))
      (cellUpper G (sourceIndex ⟨17,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum27W (by have := hn.1; omega),
    uniformNum27C (by have := hn.1; omega),
    fun _ hθ => (geometry27 hn G ht hθ).1,
    fun _ hθ => (geometry27 hn G ht hθ).2.1⟩

theorem geometry28 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨18,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 28 ≤ θ ∧ θ ≤ noiseNode G.top 29 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (493285484125205554050941/1000000000000000000000000) (494601072677613500013713/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry28W hn hc
  have hk := wideBlock1Geometry28C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply28 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨18,by decide⟩) (cellLower G (sourceIndex ⟨18,by decide⟩))
      (cellUpper G (sourceIndex ⟨18,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum28W (by have := hn.1; omega),
    uniformNum28C (by have := hn.1; omega),
    fun _ hθ => (geometry28 hn G ht hθ).1,
    fun _ hθ => (geometry28 hn G ht hθ).2.1⟩

theorem geometry29 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨19,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 29 ≤ θ ∧ θ ≤ noiseNode G.top 30 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (494474251415391466695617/1000000000000000000000000) (495794213114772586221083/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry29W hn hc
  have hk := wideBlock1Geometry29C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply29 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨19,by decide⟩) (cellLower G (sourceIndex ⟨19,by decide⟩))
      (cellUpper G (sourceIndex ⟨19,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum29W (by have := hn.1; omega),
    uniformNum29C (by have := hn.1; omega),
    fun _ hθ => (geometry29 hn G ht hθ).1,
    fun _ hθ => (geometry29 hn G ht hθ).2.1⟩

theorem geometry30 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨20,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 30 ≤ θ ∧ θ ≤ noiseNode G.top 31 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (495663018705577379340293/1000000000000000000000000) (124246838387982918107113/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry30W hn hc
  have hk := wideBlock1Geometry30C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply30 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨20,by decide⟩) (cellLower G (sourceIndex ⟨20,by decide⟩))
      (cellUpper G (sourceIndex ⟨20,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum30W (by have := hn.1; omega),
    uniformNum30C (by have := hn.1; omega),
    fun _ hθ => (geometry30 hn G ht hθ).1,
    fun _ hθ => (geometry30 hn G ht hθ).2.1⟩

theorem geometry31 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨21,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 31 ≤ θ ∧ θ ≤ noiseNode G.top 32 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (49685178599576329198497/100000000000000000000000) (498180493989090758635821/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock1Geometry31W hn hc
  have hk := wideBlock1Geometry31C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply31 {n : ℕ} (hn : n ∈ Icc 12800 13224) (G : Grid) (ht : G.top ∈ Icc (132831509352788689670147/250000000000000000000000) (132897106557386293110541/250000000000000000000000)) :
    Supply n (parameters ⟨21,by decide⟩) (cellLower G (sourceIndex ⟨21,by decide⟩))
      (cellUpper G (sourceIndex ⟨21,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum31W (by have := hn.1; omega),
    uniformNum31C (by have := hn.1; omega),
    fun _ hθ => (geometry31 hn G ht hθ).1,
    fun _ hθ => (geometry31 hn G ht hθ).2.1⟩

end BstLean.Part269.BG2
