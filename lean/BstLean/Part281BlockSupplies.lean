import BstLean.Part281Geometry0
import BstLean.Part281Geometry1
import BstLean.Part281Geometry2
import BstLean.Part281Geometry3
import BstLean.Part281UniformTI
import BstLean.Part281FrameAdapter
namespace BstLean.Part281.Geometry
open Real Set BstLean.Part263 BstLean.Part255
open BstLean.Part281.TI
theorem geometry10 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨0,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨0,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨0,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨0,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨0,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 10 ≤ θ ∧ θ ≤ noiseNode G.top 11 at hs
  norm_num [noiseNode] at hs
  have hc : B (7374914000687177714943 / 15625000000000000000000) (236618719868117662125663 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry10W hn hc
  have hk := geometry10C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply10 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨0,by decide⟩) (cellLower G (sourceIndex ⟨0,by decide⟩))
      (cellUpper G (sourceIndex ⟨0,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum10W hn.1,uniformNum10C hn.1,
    fun _ hθ => (geometry10 hn G ht hθ).1,
    fun _ hθ => (geometry10 hn G ht hθ).2.1⟩

theorem geometry11 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨1,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨1,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨1,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨1,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨1,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 11 ≤ θ ∧ θ ≤ noiseNode G.top 12 at hs
  norm_num [noiseNode] at hs
  have hc : B (118298486412094327782997 / 250000000000000000000000) (5930510541857754421609 / 12500000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry11W hn hc
  have hk := geometry11C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply11 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨1,by decide⟩) (cellLower G (sourceIndex ⟨1,by decide⟩))
      (cellUpper G (sourceIndex ⟨1,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum11W hn.1,uniformNum11C hn.1,
    fun _ hθ => (geometry11 hn G ht hθ).1,
    fun _ hθ => (geometry11 hn G ht hθ).2.1⟩

theorem geometry12 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨2,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨2,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨2,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨2,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨2,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 12 ≤ θ ∧ θ ≤ noiseNode G.top 13 at hs
  norm_num [noiseNode] at hs
  have hc : B (474393395252775248507623 / 1000000000000000000000000) (475644246961005383206113 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry12W hn hc
  have hk := geometry12C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply12 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨2,by decide⟩) (cellLower G (sourceIndex ⟨2,by decide⟩))
      (cellUpper G (sourceIndex ⟨2,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum12W hn.1,uniformNum12C hn.1,
    fun _ hθ => (geometry12 hn G ht hθ).1,
    fun _ hθ => (geometry12 hn G ht hθ).2.1⟩

theorem geometry13 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨3,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨3,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨3,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨3,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨3,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 13 ≤ θ ∧ θ ≤ noiseNode G.top 14 at hs
  norm_num [noiseNode] at hs
  have hc : B (237796422428586592941629 / 500000000000000000000000) (238423825286695206341753 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry13W hn hc
  have hk := geometry13C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply13 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨3,by decide⟩) (cellLower G (sourceIndex ⟨3,by decide⟩))
      (cellUpper G (sourceIndex ⟨3,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum13W hn.1,uniformNum13C hn.1,
    fun _ hθ => (geometry13 hn G ht hθ).1,
    fun _ hθ => (geometry13 hn G ht hθ).2.1⟩

theorem geometry14 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨4,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨4,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨4,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨4,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨4,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 14 ≤ θ ∧ θ ≤ noiseNode G.top 15 at hs
  norm_num [noiseNode] at hs
  have hc : B (476792294461571123258893 / 1000000000000000000000000) (478051054185775442160899 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry14W hn hc
  have hk := geometry14C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply14 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨4,by decide⟩) (cellLower G (sourceIndex ⟨4,by decide⟩))
      (cellUpper G (sourceIndex ⟨4,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum14W hn.1,uniformNum14C hn.1,
    fun _ hθ => (geometry14 hn G ht hθ).1,
    fun _ hθ => (geometry14 hn G ht hθ).2.1⟩

theorem geometry15 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨5,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨5,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨5,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨5,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨5,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 15 ≤ θ ∧ θ ≤ noiseNode G.top 16 at hs
  norm_num [noiseNode] at hs
  have hc : B (477991744065969060634529 / 1000000000000000000000000) (479254457798160471638293 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry15W hn hc
  have hk := geometry15C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply15 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨5,by decide⟩) (cellLower G (sourceIndex ⟨5,by decide⟩))
      (cellUpper G (sourceIndex ⟨5,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum15W hn.1,uniformNum15C hn.1,
    fun _ hθ => (geometry15 hn G ht hθ).1,
    fun _ hθ => (geometry15 hn G ht hθ).2.1⟩

theorem geometry16 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨6,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨6,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨6,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨6,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨6,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 16 ≤ θ ∧ θ ≤ noiseNode G.top 17 at hs
  norm_num [noiseNode] at hs
  have hc : B (119797798417591749502541 / 250000000000000000000000) (240228930705272750557843 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry16W hn hc
  have hk := geometry16C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply16 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨6,by decide⟩) (cellLower G (sourceIndex ⟨6,by decide⟩))
      (cellUpper G (sourceIndex ⟨6,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum16W hn.1,uniformNum16C hn.1,
    fun _ hθ => (geometry16 hn G ht hθ).1,
    fun _ hθ => (geometry16 hn G ht hθ).2.1⟩

theorem geometry17 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨7,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨7,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨7,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨7,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨7,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 17 ≤ θ ∧ θ ≤ noiseNode G.top 18 at hs
  norm_num [noiseNode] at hs
  have hc : B (480390643274764935385799 / 1000000000000000000000000) (481661265022930530593079 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry17W hn hc
  have hk := geometry17C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply17 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨7,by decide⟩) (cellLower G (sourceIndex ⟨7,by decide⟩))
      (cellUpper G (sourceIndex ⟨7,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum17W hn.1,uniformNum17C hn.1,
    fun _ hθ => (geometry17 hn G ht hθ).1,
    fun _ hθ => (geometry17 hn G ht hθ).2.1⟩

theorem geometry18 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨8,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨8,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨8,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨8,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨8,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 18 ≤ θ ∧ θ ≤ noiseNode G.top 19 at hs
  norm_num [noiseNode] at hs
  have hc : B (96318018575832574552287 / 200000000000000000000000) (60358083579414445008809 / 125000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry18W hn hc
  have hk := geometry18C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply18 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨8,by decide⟩) (cellLower G (sourceIndex ⟨8,by decide⟩))
      (cellUpper G (sourceIndex ⟨8,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum18W hn.1,uniformNum18C hn.1,
    fun _ hθ => (geometry18 hn G ht hθ).1,
    fun _ hθ => (geometry18 hn G ht hθ).2.1⟩

theorem geometry19 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨9,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨9,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨9,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨9,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨9,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 19 ≤ θ ∧ θ ≤ noiseNode G.top 20 at hs
  norm_num [noiseNode] at hs
  have hc : B (48278954248356081013707 / 100000000000000000000000) (242034036123850294773933 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry19W hn hc
  have hk := geometry19C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply19 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨9,by decide⟩) (cellLower G (sourceIndex ⟨9,by decide⟩))
      (cellUpper G (sourceIndex ⟨9,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum19W hn.1,uniformNum19C hn.1,
    fun _ hθ => (geometry19 hn G ht hθ).1,
    fun _ hθ => (geometry19 hn G ht hθ).2.1⟩

theorem geometry20 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨10,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨10,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨10,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨10,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨10,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 20 ≤ θ ∧ θ ≤ noiseNode G.top 21 at hs
  norm_num [noiseNode] at hs
  have hc : B (96797798417591749502541 / 200000000000000000000000) (485271475860085619025259 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry20W hn hc
  have hk := geometry20C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply20 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨10,by decide⟩) (cellLower G (sourceIndex ⟨10,by decide⟩))
      (cellUpper G (sourceIndex ⟨10,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum20W hn.1,uniformNum20C hn.1,
    fun _ hθ => (geometry20 hn G ht hθ).1,
    fun _ hθ => (geometry20 hn G ht hθ).2.1⟩

theorem geometry21 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨11,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨11,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨11,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨11,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨11,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 21 ≤ θ ∧ θ ≤ noiseNode G.top 22 at hs
  norm_num [noiseNode] at hs
  have hc : B (24259422084617834244417 / 50000000000000000000000) (121618719868117662125663 / 250000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry21W hn hc
  have hk := geometry21C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply21 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨11,by decide⟩) (cellLower G (sourceIndex ⟨11,by decide⟩))
      (cellUpper G (sourceIndex ⟨11,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum21W hn.1,uniformNum21C hn.1,
    fun _ hθ => (geometry21 hn G ht hθ).1,
    fun _ hθ => (geometry21 hn G ht hθ).2.1⟩

theorem geometry22 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨12,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨12,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨12,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨12,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨12,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 22 ≤ θ ∧ θ ≤ noiseNode G.top 23 at hs
  norm_num [noiseNode] at hs
  have hc : B (60798486412094327782997 / 125000000000000000000000) (97535656616971135596009 / 200000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry22W hn hc
  have hk := geometry22C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply22 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨12,by decide⟩) (cellLower G (sourceIndex ⟨12,by decide⟩))
      (cellUpper G (sourceIndex ⟨12,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum22W hn.1,uniformNum22C hn.1,
    fun _ hθ => (geometry22 hn G ht hθ).1,
    fun _ hθ => (geometry22 hn G ht hθ).2.1⟩

theorem geometry23 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨13,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨13,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨13,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨13,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨13,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 23 ≤ θ ∧ θ ≤ noiseNode G.top 24 at hs
  norm_num [noiseNode] at hs
  have hc : B (487587340901152559639611 / 1000000000000000000000000) (488881686697240707457439 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry23W hn hc
  have hk := geometry23C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply23 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨13,by decide⟩) (cellLower G (sourceIndex ⟨13,by decide⟩))
      (cellUpper G (sourceIndex ⟨13,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum23W hn.1,uniformNum23C hn.1,
    fun _ hθ => (geometry23 hn G ht hθ).1,
    fun _ hθ => (geometry23 hn G ht hθ).2.1⟩

theorem geometry24 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨14,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨14,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨14,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨14,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨14,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 24 ≤ θ ∧ θ ≤ noiseNode G.top 25 at hs
  norm_num [noiseNode] at hs
  have hc : B (244393395252775248507623 / 500000000000000000000000) (30630318144351608558427 / 62500000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry24W hn hc
  have hk := geometry24C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply24 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨14,by decide⟩) (cellLower G (sourceIndex ⟨14,by decide⟩))
      (cellUpper G (sourceIndex ⟨14,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum24W hn.1,uniformNum24C hn.1,
    fun _ hθ => (geometry24 hn G ht hθ).1,
    fun _ hθ => (geometry24 hn G ht hθ).2.1⟩

theorem geometry25 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨15,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨15,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨15,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨15,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨15,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 25 ≤ θ ∧ θ ≤ noiseNode G.top 26 at hs
  norm_num [noiseNode] at hs
  have hc : B (244993120054974217195441 / 500000000000000000000000) (19651539756880430656489 / 40000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry25W hn hc
  have hk := geometry25C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply25 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨15,by decide⟩) (cellLower G (sourceIndex ⟨15,by decide⟩))
      (cellUpper G (sourceIndex ⟨15,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum25W hn.1,uniformNum25C hn.1,
    fun _ hθ => (geometry25 hn G ht hθ).1,
    fun _ hθ => (geometry25 hn G ht hθ).2.1⟩

theorem geometry26 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨16,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨16,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨16,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨16,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨16,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 26 ≤ θ ∧ θ ≤ noiseNode G.top 27 at hs
  norm_num [noiseNode] at hs
  have hc : B (491185689714346371766517 / 1000000000000000000000000) (246245948767197897944809 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry26W hn hc
  have hk := geometry26C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply26 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨16,by decide⟩) (cellLower G (sourceIndex ⟨16,by decide⟩))
      (cellUpper G (sourceIndex ⟨16,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum26W hn.1,uniformNum26C hn.1,
    fun _ hθ => (geometry26 hn G ht hθ).1,
    fun _ hθ => (geometry26 hn G ht hθ).2.1⟩

theorem geometry27 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨17,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨17,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨17,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨17,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨17,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 27 ≤ θ ∧ θ ≤ noiseNode G.top 28 at hs
  norm_num [noiseNode] at hs
  have hc : B (61548142414843038642769 / 125000000000000000000000) (123423825286695206341753 / 250000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry27W hn hc
  have hk := geometry27C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply27 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨17,by decide⟩) (cellLower G (sourceIndex ⟨17,by decide⟩))
      (cellUpper G (sourceIndex ⟨17,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum27W hn.1,uniformNum27C hn.1,
    fun _ hθ => (geometry27 hn G ht hθ).1,
    fun _ hθ => (geometry27 hn G ht hθ).2.1⟩

theorem geometry28 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨18,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨18,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨18,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨18,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨18,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 28 ≤ θ ∧ θ ≤ noiseNode G.top 29 at hs
  norm_num [noiseNode] at hs
  have hc : B (493584588923142246517787 / 1000000000000000000000000) (98979740951833170968881 / 200000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry28W hn hc
  have hk := geometry28C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply28 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨18,by decide⟩) (cellLower G (sourceIndex ⟨18,by decide⟩))
      (cellUpper G (sourceIndex ⟨18,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum28W hn.1,uniformNum28C hn.1,
    fun _ hθ => (geometry28 hn G ht hθ).1,
    fun _ hθ => (geometry28 hn G ht hθ).2.1⟩

theorem geometry29 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨19,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨19,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨19,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨19,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨19,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 29 ≤ θ ∧ θ ≤ noiseNode G.top 30 at hs
  norm_num [noiseNode] at hs
  have hc : B (494784038527540183893423 / 1000000000000000000000000) (248051054185775442160899 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry29W hn hc
  have hk := geometry29C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply29 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨19,by decide⟩) (cellLower G (sourceIndex ⟨19,by decide⟩))
      (cellUpper G (sourceIndex ⟨19,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum29W hn.1,uniformNum29C hn.1,
    fun _ hθ => (geometry29 hn G ht hθ).1,
    fun _ hθ => (geometry29 hn G ht hθ).2.1⟩

theorem geometry30 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨20,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨20,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨20,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨20,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨20,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 30 ≤ θ ∧ θ ≤ noiseNode G.top 31 at hs
  norm_num [noiseNode] at hs
  have hc : B (247991744065969060634529 / 500000000000000000000000) (497305511983935913799191 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry30W hn hc
  have hk := geometry30C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply30 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨20,by decide⟩) (cellLower G (sourceIndex ⟨20,by decide⟩))
      (cellUpper G (sourceIndex ⟨20,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum30W hn.1,uniformNum30C hn.1,
    fun _ hθ => (geometry30 hn G ht hθ).1,
    fun _ hθ => (geometry30 hn G ht hθ).2.1⟩

theorem geometry31 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨21,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨21,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨21,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨21,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨21,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 31 ≤ θ ∧ θ ≤ noiseNode G.top 32 at hs
  norm_num [noiseNode] at hs
  have hc : B (497182937736336058644693 / 1000000000000000000000000) (99701783119264188655317 / 200000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry31W hn hc
  have hk := geometry31C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply31 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨21,by decide⟩) (cellLower G (sourceIndex ⟨21,by decide⟩))
      (cellUpper G (sourceIndex ⟨21,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum31W hn.1,uniformNum31C hn.1,
    fun _ hθ => (geometry31 hn G ht hθ).1,
    fun _ hθ => (geometry31 hn G ht hθ).2.1⟩

theorem geometry32 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨22,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨22,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨22,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 32 ≤ θ ∧ θ ≤ noiseNode G.top 33 at hs
  norm_num [noiseNode] at hs
  have hc : B (498382387340733996020329 / 1000000000000000000000000) (249856159604352986376989 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry32W hn hc
  have hk := geometry32C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨22,by decide⟩) (cellLower G (sourceIndex ⟨22,by decide⟩))
      (cellUpper G (sourceIndex ⟨22,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum32W hn.1,uniformNum32C hn.1,
    fun _ hθ => (geometry32 hn G ht hθ).1,
    fun _ hθ => (geometry32 hn G ht hθ).2.1⟩

theorem geometry33 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨23,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨23,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨23,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 33 ≤ θ ∧ θ ≤ noiseNode G.top 34 at hs
  norm_num [noiseNode] at hs
  have hc : B (124895459236282983348991 / 250000000000000000000000) (500915722821091002231371 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry33W hn hc
  have hk := geometry33C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨23,by decide⟩) (cellLower G (sourceIndex ⟨23,by decide⟩))
      (cellUpper G (sourceIndex ⟨23,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum33W hn.1,uniformNum33C hn.1,
    fun _ hθ => (geometry33 hn G ht hθ).1,
    fun _ hθ => (geometry33 hn G ht hθ).2.1⟩

theorem geometry34 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨24,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨24,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨24,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 34 ≤ θ ∧ θ ≤ noiseNode G.top 35 at hs
  norm_num [noiseNode] at hs
  have hc : B (500781286549529870771599 / 1000000000000000000000000) (125529781608369007927191 / 250000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry34W hn hc
  have hk := geometry34C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨24,by decide⟩) (cellLower G (sourceIndex ⟨24,by decide⟩))
      (cellUpper G (sourceIndex ⟨24,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum34W hn.1,uniformNum34C hn.1,
    fun _ hθ => (geometry34 hn G ht hθ).1,
    fun _ hθ => (geometry34 hn G ht hθ).2.1⟩

theorem geometry35 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨25,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨25,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨25,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 35 ≤ θ ∧ θ ≤ noiseNode G.top 36 at hs
  norm_num [noiseNode] at hs
  have hc : B (250990368076963904073617 / 500000000000000000000000) (251661265022930530593079 / 500000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry35W hn hc
  have hk := geometry35C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨25,by decide⟩) (cellLower G (sourceIndex ⟨25,by decide⟩))
      (cellUpper G (sourceIndex ⟨25,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum35W hn.1,uniformNum35C hn.1,
    fun _ hθ => (geometry35 hn G ht hθ).1,
    fun _ hθ => (geometry35 hn G ht hθ).2.1⟩

theorem geometry36 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨26,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨26,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨26,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 36 ≤ θ ∧ θ ≤ noiseNode G.top 37 at hs
  norm_num [noiseNode] at hs
  have hc : B (50318018575832574552287 / 100000000000000000000000) (504525933658246090663551 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry36W hn hc
  have hk := geometry36C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨26,by decide⟩) (cellLower G (sourceIndex ⟨26,by decide⟩))
      (cellUpper G (sourceIndex ⟨26,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum36W hn.1,uniformNum36C hn.1,
    fun _ hθ => (geometry36 hn G ht hθ).1,
    fun _ hθ => (geometry36 hn G ht hθ).2.1⟩

theorem geometry37 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨27,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨27,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨27,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 37 ≤ θ ∧ θ ≤ noiseNode G.top 38 at hs
  norm_num [noiseNode] at hs
  have hc : B (100875927072544736579701 / 200000000000000000000000) (31608083579414445008809 / 62500000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry37W hn hc
  have hk := geometry37C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨27,by decide⟩) (cellLower G (sourceIndex ⟨27,by decide⟩))
      (cellUpper G (sourceIndex ⟨27,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum37W hn.1,uniformNum37C hn.1,
    fun _ hθ => (geometry37 hn G ht hθ).1,
    fun _ hθ => (geometry37 hn G ht hθ).2.1⟩

theorem geometry38 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨28,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨28,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨28,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 38 ≤ θ ∧ θ ≤ noiseNode G.top 39 at hs
  norm_num [noiseNode] at hs
  have hc : B (25278954248356081013707 / 50000000000000000000000) (506932740883016149618337 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry38W hn hc
  have hk := geometry38C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨28,by decide⟩) (cellLower G (sourceIndex ⟨28,by decide⟩))
      (cellUpper G (sourceIndex ⟨28,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum38W hn.1,uniformNum38C hn.1,
    fun _ hθ => (geometry38 hn G ht hθ).1,
    fun _ hθ => (geometry38 hn G ht hθ).2.1⟩

theorem geometry39 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨29,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨29,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨29,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 39 ≤ θ ∧ θ ≤ noiseNode G.top 40 at hs
  norm_num [noiseNode] at hs
  have hc : B (31673658410719972353111 / 62500000000000000000000) (508136144495401179095731 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry39W hn hc
  have hk := geometry39C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨29,by decide⟩) (cellLower G (sourceIndex ⟨29,by decide⟩))
      (cellUpper G (sourceIndex ⟨29,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum39W hn.1,uniformNum39C hn.1,
    fun _ hθ => (geometry39 hn G ht hθ).1,
    fun _ hθ => (geometry39 hn G ht hθ).2.1⟩

theorem geometry40 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨30,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨30,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨30,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 40 ≤ θ ∧ θ ≤ noiseNode G.top 41 at hs
  norm_num [noiseNode] at hs
  have hc : B (507977984175917495025411 / 1000000000000000000000000) (127334887026946552143281 / 250000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry40W hn hc
  have hk := geometry40C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨30,by decide⟩) (cellLower G (sourceIndex ⟨30,by decide⟩))
      (cellUpper G (sourceIndex ⟨30,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum40W hn.1,uniformNum40C hn.1,
    fun _ hθ => (geometry40 hn G ht hθ).1,
    fun _ hθ => (geometry40 hn G ht hθ).2.1⟩

theorem geometry41 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨31,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨31,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨31,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 41 ≤ θ ∧ θ ≤ noiseNode G.top 42 at hs
  norm_num [noiseNode] at hs
  have hc : B (254588716890157716200523 / 500000000000000000000000) (510542951720171238050517 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry41W hn hc
  have hk := geometry41C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨31,by decide⟩) (cellLower G (sourceIndex ⟨31,by decide⟩))
      (cellUpper G (sourceIndex ⟨31,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum41W hn.1,uniformNum41C hn.1,
    fun _ hθ => (geometry41 hn G ht hθ).1,
    fun _ hθ => (geometry41 hn G ht hθ).2.1⟩

theorem geometry42 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨32,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨32,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨32,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 42 ≤ θ ∧ θ ≤ noiseNode G.top 43 at hs
  norm_num [noiseNode] at hs
  have hc : B (510376883384713369776681 / 1000000000000000000000000) (51174635533255626752791 / 100000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry42W hn hc
  have hk := geometry42C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨32,by decide⟩) (cellLower G (sourceIndex ⟨32,by decide⟩))
      (cellUpper G (sourceIndex ⟨32,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum42W hn.1,uniformNum42C hn.1,
    fun _ hθ => (geometry42 hn G ht hθ).1,
    fun _ hθ => (geometry42 hn G ht hθ).2.1⟩

theorem geometry43 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨33,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨33,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨33,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 43 ≤ θ ∧ θ ≤ noiseNode G.top 44 at hs
  norm_num [noiseNode] at hs
  have hc : B (511576332989111307152317 / 1000000000000000000000000) (64118719868117662125663 / 125000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry43W hn hc
  have hk := geometry43C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨33,by decide⟩) (cellLower G (sourceIndex ⟨33,by decide⟩))
      (cellUpper G (sourceIndex ⟨33,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum43W hn.1,uniformNum43C hn.1,
    fun _ hθ => (geometry43 hn G ht hθ).1,
    fun _ hθ => (geometry43 hn G ht hθ).2.1⟩

theorem geometry44 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨34,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨34,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨34,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 44 ≤ θ ∧ θ ≤ noiseNode G.top 45 at hs
  norm_num [noiseNode] at hs
  have hc : B (32048486412094327782997 / 62500000000000000000000) (514153162557326326482697 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry44W hn hc
  have hk := geometry44C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨34,by decide⟩) (cellLower G (sourceIndex ⟨34,by decide⟩))
      (cellUpper G (sourceIndex ⟨34,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum44W hn.1,uniformNum44C hn.1,
    fun _ hθ => (geometry44 hn G ht hθ).1,
    fun _ hθ => (geometry44 hn G ht hθ).2.1⟩

theorem geometry45 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨35,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨35,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨35,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 45 ≤ θ ∧ θ ≤ noiseNode G.top 46 at hs
  norm_num [noiseNode] at hs
  have hc : B (513975232197907181903587 / 1000000000000000000000000) (51535656616971135596009 / 100000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry45W hn hc
  have hk := geometry45C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨35,by decide⟩) (cellLower G (sourceIndex ⟨35,by decide⟩))
      (cellUpper G (sourceIndex ⟨35,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum45W hn.1,uniformNum45C hn.1,
    fun _ hθ => (geometry45 hn G ht hθ).1,
    fun _ hθ => (geometry45 hn G ht hθ).2.1⟩

theorem geometry46 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨36,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨36,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨36,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 46 ≤ θ ∧ θ ≤ noiseNode G.top 47 at hs
  norm_num [noiseNode] at hs
  have hc : B (515174681802305119279223 / 1000000000000000000000000) (516559969782096385437483 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry46W hn hc
  have hk := geometry46C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨36,by decide⟩) (cellLower G (sourceIndex ⟨36,by decide⟩))
      (cellUpper G (sourceIndex ⟨36,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum46W hn.1,uniformNum46C hn.1,
    fun _ hθ => (geometry46 hn G ht hθ).1,
    fun _ hθ => (geometry46 hn G ht hθ).2.1⟩

theorem geometry47 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨37,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨37,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨37,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 47 ≤ θ ∧ θ ≤ noiseNode G.top 48 at hs
  norm_num [noiseNode] at hs
  have hc : B (258187065703351528327429 / 500000000000000000000000) (517763373394481414914877 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry47W hn hc
  have hk := geometry47C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨37,by decide⟩) (cellLower G (sourceIndex ⟨37,by decide⟩))
      (cellUpper G (sourceIndex ⟨37,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum47W hn.1,uniformNum47C hn.1,
    fun _ hθ => (geometry47 hn G ht hθ).1,
    fun _ hθ => (geometry47 hn G ht hθ).2.1⟩

theorem geometry48 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨38,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨38,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨38,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 48 ≤ θ ∧ θ ≤ noiseNode G.top 49 at hs
  norm_num [noiseNode] at hs
  have hc : B (517573581011100994030493 / 1000000000000000000000000) (51896677700686644439227 / 100000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry48W hn hc
  have hk := geometry48C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨38,by decide⟩) (cellLower G (sourceIndex ⟨38,by decide⟩))
      (cellUpper G (sourceIndex ⟨38,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum48W hn.1,uniformNum48C hn.1,
    fun _ hθ => (geometry48 hn G ht hθ).1,
    fun _ hθ => (geometry48 hn G ht hθ).2.1⟩

theorem geometry49 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨39,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨39,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨39,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 49 ≤ θ ∧ θ ≤ noiseNode G.top 50 at hs
  norm_num [noiseNode] at hs
  have hc : B (32423314413468683212883 / 62500000000000000000000) (520170180619251473869663 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry49W hn hc
  have hk := geometry49C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨39,by decide⟩) (cellLower G (sourceIndex ⟨39,by decide⟩))
      (cellUpper G (sourceIndex ⟨39,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum49W hn.1,uniformNum49C hn.1,
    fun _ hθ => (geometry49 hn G ht hθ).1,
    fun _ hθ => (geometry49 hn G ht hθ).2.1⟩

theorem geometry50 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨40,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨40,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨40,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 50 ≤ θ ∧ θ ≤ noiseNode G.top 51 at hs
  norm_num [noiseNode] at hs
  have hc : B (129993120054974217195441 / 250000000000000000000000) (32585849014477281459191 / 62500000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry50W hn hc
  have hk := geometry50C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨40,by decide⟩) (cellLower G (sourceIndex ⟨40,by decide⟩))
      (cellUpper G (sourceIndex ⟨40,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum50W hn.1,uniformNum50C hn.1,
    fun _ hθ => (geometry50 hn G ht hθ).1,
    fun _ hθ => (geometry50 hn G ht hθ).2.1⟩

theorem geometry51 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨41,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨41,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨41,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 51 ≤ θ ∧ θ ≤ noiseNode G.top 52 at hs
  norm_num [noiseNode] at hs
  have hc : B (521171929824294806157399 / 1000000000000000000000000) (10451539756880430656489 / 20000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry51W hn hc
  have hk := geometry51C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨41,by decide⟩) (cellLower G (sourceIndex ⟨41,by decide⟩))
      (cellUpper G (sourceIndex ⟨41,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum51W hn.1,uniformNum51C hn.1,
    fun _ hθ => (geometry51 hn G ht hθ).1,
    fun _ hθ => (geometry51 hn G ht hθ).2.1⟩

theorem geometry52 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (BstLean.Part281.TI.parameters ⟨42,by decide⟩).wlo (BstLean.Part281.TI.parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (BstLean.Part281.TI.parameters ⟨42,by decide⟩).clo (BstLean.Part281.TI.parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters ⟨42,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 52 ≤ θ ∧ θ ≤ noiseNode G.top 53 at hs
  norm_num [noiseNode] at hs
  have hc : B (261185689714346371766517 / 500000000000000000000000) (523780391456406562301843 / 1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1,hs.1]),(by linarith [ht.2,hs.2])⟩
  have hw := geometry52W hn hc
  have hk := geometry52C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) :
    Supply n (BstLean.Part281.TI.parameters ⟨42,by decide⟩) (cellLower G (sourceIndex ⟨42,by decide⟩))
      (cellUpper G (sourceIndex ⟨42,by decide⟩)) :=
  ⟨BstLean.Part281.TI.parameters_valid _,uniformNum52W hn.1,uniformNum52C hn.1,
    fun _ hθ => (geometry52 hn G ht hθ).1,
    fun _ hθ => (geometry52 hn G ht hθ).2.1⟩

theorem supplies {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) (j : Fin 43) :
    Supply n (BstLean.Part281.TI.parameters j) (cellLower G (sourceIndex j))
      (cellUpper G (sourceIndex j)) := by
  match j with
  | ⟨0,_⟩ => exact supply10 hn G ht
  | ⟨1,_⟩ => exact supply11 hn G ht
  | ⟨2,_⟩ => exact supply12 hn G ht
  | ⟨3,_⟩ => exact supply13 hn G ht
  | ⟨4,_⟩ => exact supply14 hn G ht
  | ⟨5,_⟩ => exact supply15 hn G ht
  | ⟨6,_⟩ => exact supply16 hn G ht
  | ⟨7,_⟩ => exact supply17 hn G ht
  | ⟨8,_⟩ => exact supply18 hn G ht
  | ⟨9,_⟩ => exact supply19 hn G ht
  | ⟨10,_⟩ => exact supply20 hn G ht
  | ⟨11,_⟩ => exact supply21 hn G ht
  | ⟨12,_⟩ => exact supply22 hn G ht
  | ⟨13,_⟩ => exact supply23 hn G ht
  | ⟨14,_⟩ => exact supply24 hn G ht
  | ⟨15,_⟩ => exact supply25 hn G ht
  | ⟨16,_⟩ => exact supply26 hn G ht
  | ⟨17,_⟩ => exact supply27 hn G ht
  | ⟨18,_⟩ => exact supply28 hn G ht
  | ⟨19,_⟩ => exact supply29 hn G ht
  | ⟨20,_⟩ => exact supply30 hn G ht
  | ⟨21,_⟩ => exact supply31 hn G ht
  | ⟨22,_⟩ => exact supply32 hn G ht
  | ⟨23,_⟩ => exact supply33 hn G ht
  | ⟨24,_⟩ => exact supply34 hn G ht
  | ⟨25,_⟩ => exact supply35 hn G ht
  | ⟨26,_⟩ => exact supply36 hn G ht
  | ⟨27,_⟩ => exact supply37 hn G ht
  | ⟨28,_⟩ => exact supply38 hn G ht
  | ⟨29,_⟩ => exact supply39 hn G ht
  | ⟨30,_⟩ => exact supply40 hn G ht
  | ⟨31,_⟩ => exact supply41 hn G ht
  | ⟨32,_⟩ => exact supply42 hn G ht
  | ⟨33,_⟩ => exact supply43 hn G ht
  | ⟨34,_⟩ => exact supply44 hn G ht
  | ⟨35,_⟩ => exact supply45 hn G ht
  | ⟨36,_⟩ => exact supply46 hn G ht
  | ⟨37,_⟩ => exact supply47 hn G ht
  | ⟨38,_⟩ => exact supply48 hn G ht
  | ⟨39,_⟩ => exact supply49 hn G ht
  | ⟨40,_⟩ => exact supply50 hn G ht
  | ⟨41,_⟩ => exact supply51 hn G ht
  | ⟨42,_⟩ => exact supply52 hn G ht
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem radii {n : ℕ} (hn : n ∈ Icc 11883 12224) (G : Grid) (ht : G.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000)) (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex j)) :
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (BstLean.Part281.TI.parameters j).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (BstLean.Part281.TI.parameters j).cRadius := by
  match j with
  | ⟨0,_⟩ => exact (geometry10 hn G ht hθ).2.2
  | ⟨1,_⟩ => exact (geometry11 hn G ht hθ).2.2
  | ⟨2,_⟩ => exact (geometry12 hn G ht hθ).2.2
  | ⟨3,_⟩ => exact (geometry13 hn G ht hθ).2.2
  | ⟨4,_⟩ => exact (geometry14 hn G ht hθ).2.2
  | ⟨5,_⟩ => exact (geometry15 hn G ht hθ).2.2
  | ⟨6,_⟩ => exact (geometry16 hn G ht hθ).2.2
  | ⟨7,_⟩ => exact (geometry17 hn G ht hθ).2.2
  | ⟨8,_⟩ => exact (geometry18 hn G ht hθ).2.2
  | ⟨9,_⟩ => exact (geometry19 hn G ht hθ).2.2
  | ⟨10,_⟩ => exact (geometry20 hn G ht hθ).2.2
  | ⟨11,_⟩ => exact (geometry21 hn G ht hθ).2.2
  | ⟨12,_⟩ => exact (geometry22 hn G ht hθ).2.2
  | ⟨13,_⟩ => exact (geometry23 hn G ht hθ).2.2
  | ⟨14,_⟩ => exact (geometry24 hn G ht hθ).2.2
  | ⟨15,_⟩ => exact (geometry25 hn G ht hθ).2.2
  | ⟨16,_⟩ => exact (geometry26 hn G ht hθ).2.2
  | ⟨17,_⟩ => exact (geometry27 hn G ht hθ).2.2
  | ⟨18,_⟩ => exact (geometry28 hn G ht hθ).2.2
  | ⟨19,_⟩ => exact (geometry29 hn G ht hθ).2.2
  | ⟨20,_⟩ => exact (geometry30 hn G ht hθ).2.2
  | ⟨21,_⟩ => exact (geometry31 hn G ht hθ).2.2
  | ⟨22,_⟩ => exact (geometry32 hn G ht hθ).2.2
  | ⟨23,_⟩ => exact (geometry33 hn G ht hθ).2.2
  | ⟨24,_⟩ => exact (geometry34 hn G ht hθ).2.2
  | ⟨25,_⟩ => exact (geometry35 hn G ht hθ).2.2
  | ⟨26,_⟩ => exact (geometry36 hn G ht hθ).2.2
  | ⟨27,_⟩ => exact (geometry37 hn G ht hθ).2.2
  | ⟨28,_⟩ => exact (geometry38 hn G ht hθ).2.2
  | ⟨29,_⟩ => exact (geometry39 hn G ht hθ).2.2
  | ⟨30,_⟩ => exact (geometry40 hn G ht hθ).2.2
  | ⟨31,_⟩ => exact (geometry41 hn G ht hθ).2.2
  | ⟨32,_⟩ => exact (geometry42 hn G ht hθ).2.2
  | ⟨33,_⟩ => exact (geometry43 hn G ht hθ).2.2
  | ⟨34,_⟩ => exact (geometry44 hn G ht hθ).2.2
  | ⟨35,_⟩ => exact (geometry45 hn G ht hθ).2.2
  | ⟨36,_⟩ => exact (geometry46 hn G ht hθ).2.2
  | ⟨37,_⟩ => exact (geometry47 hn G ht hθ).2.2
  | ⟨38,_⟩ => exact (geometry48 hn G ht hθ).2.2
  | ⟨39,_⟩ => exact (geometry49 hn G ht hθ).2.2
  | ⟨40,_⟩ => exact (geometry50 hn G ht hθ).2.2
  | ⟨41,_⟩ => exact (geometry51 hn G ht hθ).2.2
  | ⟨42,_⟩ => exact (geometry52 hn G ht hθ).2.2
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def covarianceInputs {n : ℕ} (hn : n ∈ Icc 11883 12224)
    (R : ScalarRow n) (ht : R.grid.top ∈ Icc (531966976263876242538117 / 1000000000000000000000000) (106440843348620353728719 / 200000000000000000000000))
    (A : BstLean.Part281.FrameRepair n R) :
    BstLean.Part277.CovarianceInputsP (528/1000) n R.grid
      BstLean.Part281.TI.parameters (BstLean.Part281.caps A) :=
  BstLean.Part281.covarianceInputs_from_supplies hn.1 A (supplies hn R.grid ht)
    (fun j _ hθ => radii hn R.grid ht j hθ)
end BstLean.Part281.Geometry
