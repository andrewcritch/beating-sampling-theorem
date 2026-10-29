import BstLean.Part269WideGeometry0_0
import BstLean.Part269WideGeometry0_1
import BstLean.Part264bUniformTI
import BstLean.Part264Covariance
namespace BstLean.Part269.BG1
open Real Set BstLean.Part263 BstLean.Part264 BstLean.Part264b BstLean.Part255
theorem geometry32 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨22,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 32 ≤ θ ∧ θ ≤ noiseNode G.top 33 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (498180832402564154159197/1000000000000000000000000) (62440727946197252414437/125000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry32W hn hc
  have hk := wideBlock0Geometry32C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨22,by decide⟩) (cellLower G (sourceIndex ⟨22,by decide⟩))
      (cellUpper G (sourceIndex ⟨22,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum32W (by have := hn.1; omega),
    uniformNum32C (by have := hn.1; omega),
    fun _ hθ => (geometry32 hn G ht hθ).1,
    fun _ hθ => (geometry32 hn G ht hθ).2.1⟩

theorem geometry33 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨23,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 33 ≤ θ ∧ θ ≤ noiseNode G.top 34 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (15605436981723258874271/31250000000000000000000) (100144715159791834283193/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry33W hn hc
  have hk := wideBlock0Geometry33C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨23,by decide⟩) (cellLower G (sourceIndex ⟨23,by decide⟩))
      (cellUpper G (sourceIndex ⟨23,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum33W (by have := hn.1; omega),
    uniformNum33C (by have := hn.1; omega),
    fun _ hθ => (geometry33 hn G ht hθ).1,
    fun _ hθ => (geometry33 hn G ht hθ).2.1⟩

theorem geometry34 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨24,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 34 ≤ θ ∧ θ ≤ noiseNode G.top 35 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (500567134427724413794147/1000000000000000000000000) (100384265605668064703287/200000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry34W hn hc
  have hk := wideBlock0Geometry34C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨24,by decide⟩) (cellLower G (sourceIndex ⟨24,by decide⟩))
      (cellUpper G (sourceIndex ⟨24,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum34W (by have := hn.1; omega),
    uniformNum34C (by have := hn.1; omega),
    fun _ hθ => (geometry34 hn G ht hθ).1,
    fun _ hθ => (geometry34 hn G ht hθ).2.1⟩

theorem geometry35 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨25,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 35 ≤ θ ∧ θ ≤ noiseNode G.top 36 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (250880142720152271805811/500000000000000000000000) (62889885032215184452113/125000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry35W hn hc
  have hk := wideBlock0Geometry35C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨25,by decide⟩) (cellLower G (sourceIndex ⟨25,by decide⟩))
      (cellUpper G (sourceIndex ⟨25,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum35W (by have := hn.1; omega),
    uniformNum35C (by have := hn.1; omega),
    fun _ hθ => (geometry35 hn G ht hθ).1,
    fun _ hθ => (geometry35 hn G ht hθ).2.1⟩

theorem geometry36 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨26,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 36 ≤ θ ∧ θ ≤ noiseNode G.top 37 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (502953436452884673429097/1000000000000000000000000) (252158416243551313858687/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry36W hn hc
  have hk := wideBlock0Geometry36C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨26,by decide⟩) (cellLower G (sourceIndex ⟨26,by decide⟩))
      (cellUpper G (sourceIndex ⟨26,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum36W (by have := hn.1; omega),
    uniformNum36C (by have := hn.1; omega),
    fun _ hθ => (geometry36 hn G ht hθ).1,
    fun _ hθ => (geometry36 hn G ht hθ).2.1⟩

theorem geometry37 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨27,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 37 ≤ θ ∧ θ ≤ noiseNode G.top 38 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (126036646866366200811643/250000000000000000000000) (505514584716483779817843/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry37W hn hc
  have hk := wideBlock0Geometry37C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨27,by decide⟩) (cellLower G (sourceIndex ⟨27,by decide⟩))
      (cellUpper G (sourceIndex ⟨27,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum37W (by have := hn.1; omega),
    uniformNum37C (by have := hn.1; omega),
    fun _ hθ => (geometry37 hn G ht hθ).1,
    fun _ hθ => (geometry37 hn G ht hθ).2.1⟩

theorem geometry38 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨28,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 38 ≤ θ ∧ θ ≤ noiseNode G.top 39 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (505339738478044933064047/1000000000000000000000000) (506712336945864931918313/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry38W hn hc
  have hk := wideBlock0Geometry38C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨28,by decide⟩) (cellLower G (sourceIndex ⟨28,by decide⟩))
      (cellUpper G (sourceIndex ⟨28,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum38W (by have := hn.1; omega),
    uniformNum38C (by have := hn.1; omega),
    fun _ hθ => (geometry38 hn G ht hθ).1,
    fun _ hθ => (geometry38 hn G ht hθ).2.1⟩

theorem geometry39 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨29,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 39 ≤ θ ∧ θ ≤ noiseNode G.top 40 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (253266444745312531440761/500000000000000000000000) (507910089175246084018783/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry39W hn hc
  have hk := wideBlock0Geometry39C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨29,by decide⟩) (cellLower G (sourceIndex ⟨29,by decide⟩))
      (cellUpper G (sourceIndex ⟨29,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum39W (by have := hn.1; omega),
    uniformNum39C (by have := hn.1; omega),
    fun _ hθ => (geometry39 hn G ht hθ).1,
    fun _ hθ => (geometry39 hn G ht hθ).2.1⟩

theorem geometry40 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨30,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 40 ≤ θ ∧ θ ≤ noiseNode G.top 41 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (507726040503205192698997/1000000000000000000000000) (127276960351156809029813/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry40W hn hc
  have hk := wideBlock0Geometry40C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨30,by decide⟩) (cellLower G (sourceIndex ⟨30,by decide⟩))
      (cellUpper G (sourceIndex ⟨30,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum40W (by have := hn.1; omega),
    uniformNum40C (by have := hn.1; omega),
    fun _ hθ => (geometry40 hn G ht hθ).1,
    fun _ hθ => (geometry40 hn G ht hθ).2.1⟩

theorem geometry41 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨31,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 41 ≤ θ ∧ θ ≤ noiseNode G.top 42 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (63614898939473165314559/125000000000000000000000) (255152796817004194109861/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry41W hn hc
  have hk := wideBlock0Geometry41C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨31,by decide⟩) (cellLower G (sourceIndex ⟨31,by decide⟩))
      (cellUpper G (sourceIndex ⟨31,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum41W (by have := hn.1; omega),
    uniformNum41C (by have := hn.1; omega),
    fun _ hθ => (geometry41 hn G ht hθ).1,
    fun _ hθ => (geometry41 hn G ht hθ).2.1⟩

theorem geometry42 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨32,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 42 ≤ θ ∧ θ ≤ noiseNode G.top 43 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (510112342528365452333947/1000000000000000000000000) (511503345863389540320191/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry42W hn hc
  have hk := wideBlock0Geometry42C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨32,by decide⟩) (cellLower G (sourceIndex ⟨32,by decide⟩))
      (cellUpper G (sourceIndex ⟨32,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum42W (by have := hn.1; omega),
    uniformNum42C (by have := hn.1; omega),
    fun _ hθ => (geometry42 hn G ht hθ).1,
    fun _ hθ => (geometry42 hn G ht hθ).2.1⟩

theorem geometry43 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨33,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 43 ≤ θ ∧ θ ≤ noiseNode G.top 44 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (255652746770472791075711/500000000000000000000000) (512701098092770692420661/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry43W hn hc
  have hk := wideBlock0Geometry43C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨33,by decide⟩) (cellLower G (sourceIndex ⟨33,by decide⟩))
      (cellUpper G (sourceIndex ⟨33,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum43W (by have := hn.1; omega),
    uniformNum43C (by have := hn.1; omega),
    fun _ hθ => (geometry43 hn G ht hθ).1,
    fun _ hθ => (geometry43 hn G ht hθ).2.1⟩

theorem geometry44 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨34,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 44 ≤ θ ∧ θ ≤ noiseNode G.top 45 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (512498644553525711968897/1000000000000000000000000) (51389885032215184452113/100000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry44W hn hc
  have hk := wideBlock0Geometry44C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨34,by decide⟩) (cellLower G (sourceIndex ⟨34,by decide⟩))
      (cellUpper G (sourceIndex ⟨34,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum44W (by have := hn.1; omega),
    uniformNum44C (by have := hn.1; omega),
    fun _ hθ => (geometry44 hn G ht hθ).1,
    fun _ hθ => (geometry44 hn G ht hθ).2.1⟩

theorem geometry45 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨35,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 45 ≤ θ ∧ θ ≤ noiseNode G.top 46 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (513691795566105841786371/1000000000000000000000000) (643870753189416245777/1250000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry45W hn hc
  have hk := wideBlock0Geometry45C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨35,by decide⟩) (cellLower G (sourceIndex ⟨35,by decide⟩))
      (cellUpper G (sourceIndex ⟨35,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum45W (by have := hn.1; omega),
    uniformNum45C (by have := hn.1; omega),
    fun _ hθ => (geometry45 hn G ht hθ).1,
    fun _ hθ => (geometry45 hn G ht hθ).2.1⟩

theorem geometry46 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨36,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 46 ≤ θ ∧ θ ≤ noiseNode G.top 47 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (257442473289342985801923/500000000000000000000000) (516294354780914148722069/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry46W hn hc
  have hk := wideBlock0Geometry46C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨36,by decide⟩) (cellLower G (sourceIndex ⟨36,by decide⟩))
      (cellUpper G (sourceIndex ⟨36,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum46W (by have := hn.1; omega),
    uniformNum46C (by have := hn.1; omega),
    fun _ hθ => (geometry46 hn G ht hθ).1,
    fun _ hθ => (geometry46 hn G ht hθ).2.1⟩

theorem geometry47 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨37,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 47 ≤ θ ∧ θ ≤ noiseNode G.top 48 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (516078097591266101421321/1000000000000000000000000) (517492107010295300822539/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry47W hn hc
  have hk := wideBlock0Geometry47C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨37,by decide⟩) (cellLower G (sourceIndex ⟨37,by decide⟩))
      (cellUpper G (sourceIndex ⟨37,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum47W (by have := hn.1; omega),
    uniformNum47C (by have := hn.1; omega),
    fun _ hθ => (geometry47 hn G ht hθ).1,
    fun _ hθ => (geometry47 hn G ht hθ).2.1⟩

theorem geometry48 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨38,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 48 ≤ θ ∧ θ ≤ noiseNode G.top 49 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (129317812150961557809699/250000000000000000000000) (4052264525309972288461/7812500000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry48W hn hc
  have hk := wideBlock0Geometry48C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨38,by decide⟩) (cellLower G (sourceIndex ⟨38,by decide⟩))
      (cellUpper G (sourceIndex ⟨38,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum48W (by have := hn.1; omega),
    uniformNum48C (by have := hn.1; omega),
    fun _ hθ => (geometry48 hn G ht hθ).1,
    fun _ hθ => (geometry48 hn G ht hθ).2.1⟩

theorem geometry49 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨39,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 49 ≤ θ ∧ θ ≤ noiseNode G.top 50 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (518464399616426361056271/1000000000000000000000000) (259943805734528802511739/500000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry49W hn hc
  have hk := wideBlock0Geometry49C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨39,by decide⟩) (cellLower G (sourceIndex ⟨39,by decide⟩))
      (cellUpper G (sourceIndex ⟨39,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum49W (by have := hn.1; omega),
    uniformNum49C (by have := hn.1; omega),
    fun _ hθ => (geometry49 hn G ht hθ).1,
    fun _ hθ => (geometry49 hn G ht hθ).2.1⟩

theorem geometry50 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨40,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 50 ≤ θ ∧ θ ≤ noiseNode G.top 51 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (259828775314503245436873/500000000000000000000000) (130271340924609689280987/250000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry50W hn hc
  have hk := wideBlock0Geometry50C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨40,by decide⟩) (cellLower G (sourceIndex ⟨40,by decide⟩))
      (cellUpper G (sourceIndex ⟨40,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum50W (by have := hn.1; omega),
    uniformNum50C (by have := hn.1; omega),
    fun _ hθ => (geometry50 hn G ht hθ).1,
    fun _ hθ => (geometry50 hn G ht hθ).2.1⟩

theorem geometry51 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨41,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 51 ≤ θ ∧ θ ≤ noiseNode G.top 52 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (520850701641586620691221/1000000000000000000000000) (522283115927819909224417/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry51W hn hc
  have hk := wideBlock0Geometry51C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨41,by decide⟩) (cellLower G (sourceIndex ⟨41,by decide⟩))
      (cellUpper G (sourceIndex ⟨41,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum51W (by have := hn.1; omega),
    uniformNum51C (by have := hn.1; omega),
    fun _ hθ => (geometry51 hn G ht hθ).1,
    fun _ hθ => (geometry51 hn G ht hθ).2.1⟩

theorem geometry52 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) {θ : ℝ}
    (hθ : θ ∈ cell G (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨42,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode G.top 52 ≤ θ ∧ θ ≤ noiseNode G.top 53 at hs
  norm_num [noiseNode] at hs
  have hc : BstLean.Part255.B (65255481581770843813587/125000000000000000000000) (523480868157201061324887/1000000000000000000000000) θ :=
    ⟨(by linarith [ht.1, hs.1]), (by linarith [ht.2, hs.2])⟩
  have hw := wideBlock0Geometry52W hn hc
  have hk := wideBlock0Geometry52C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 {n : ℕ} (hn : n ∈ Icc 12375 12799) (G : Grid) (ht : G.top ∈ Icc (33224316297175486815531/62500000000000000000000) (531865133762869126028173/1000000000000000000000000)) :
    Supply n (parameters ⟨42,by decide⟩) (cellLower G (sourceIndex ⟨42,by decide⟩))
      (cellUpper G (sourceIndex ⟨42,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum52W (by have := hn.1; omega),
    uniformNum52C (by have := hn.1; omega),
    fun _ hθ => (geometry52 hn G ht hθ).1,
    fun _ hθ => (geometry52 hn G ht hθ).2.1⟩

end BstLean.Part269.BG1
