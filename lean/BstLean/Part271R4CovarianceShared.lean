import BstLean.Part271R4GeometryShared0
import BstLean.Part271R4GeometryShared1
import BstLean.Part271R4GeometryShared2
import BstLean.Part271R4GeometryShared3
import BstLean.Part271R4Block
import BstLean.Part264bUniformTI
import BstLean.Part264Covariance

/-! One covariance transfer for every R4 block and every allowed grid top. -/
namespace BstLean.Part271.R4.SharedCovariance
open Real Set BstLean.Part263 BstLean.Part264 BstLean.Part264b BstLean.Part255

theorem geometry10 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨0,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 10 ≤ θ ∧ θ ≤ noiseNode R.grid.top 11 at hs
  have hc : BstLean.Part255.B (565958839397/1200000000000) (1135383190883/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry10W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry10C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply10 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨0,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨0,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨0,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum10W (by have := hn.1; omega),
    uniformNum10C (by have := hn.1; omega),
    fun _ hθ => (geometry10 hn R htop hθ).1,
    fun _ hθ => (geometry10 hn R htop hθ).2.1⟩

theorem geometry11 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨1,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 11 ≤ θ ∧ θ ≤ noiseNode R.grid.top 12 at hs
  have hc : BstLean.Part255.B (5673547233367/12000000000000) (94853017353/200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry11W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry11C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply11 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨1,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨1,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨1,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum11W (by have := hn.1; omega),
    uniformNum11C (by have := hn.1; omega),
    fun _ hθ => (geometry11 hn R htop hθ).1,
    fun _ hθ => (geometry11 hn R htop hθ).2.1⟩

theorem geometry12 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨2,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 12 ≤ θ ∧ θ ≤ noiseNode R.grid.top 13 at hs
  have hc : BstLean.Part255.B (473958839397/1000000000000) (1141089225589/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry12W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry12C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply12 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨2,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨2,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨2,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum12W (by have := hn.1; omega),
    uniformNum12C (by have := hn.1; omega),
    fun _ hθ => (geometry12 hn R htop hθ).1,
    fun _ hθ => (geometry12 hn R htop hθ).2.1⟩

theorem geometry13 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨3,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 13 ≤ θ ∧ θ ≤ noiseNode R.grid.top 14 at hs
  have hc : BstLean.Part255.B (5701464912161/12000000000000) (571971121471/1200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry13W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry13C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply13 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨3,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨3,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨3,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum13W (by have := hn.1; omega),
    uniformNum13C (by have := hn.1; omega),
    fun _ hθ => (geometry13 hn R htop hθ).1,
    fun _ hθ => (geometry13 hn R htop hθ).2.1⟩

theorem geometry14 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨4,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 14 ≤ θ ∧ θ ≤ noiseNode R.grid.top 15 at hs
  have hc : BstLean.Part255.B (2857711875779/6000000000000) (76453017353/160000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry14W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry14C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply14 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨4,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨4,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨4,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum14W (by have := hn.1; omega),
    uniformNum14C (by have := hn.1; omega),
    fun _ hθ => (geometry14 hn R htop hθ).1,
    fun _ hθ => (geometry14 hn R htop hθ).2.1⟩

theorem geometry15 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨5,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 15 ≤ θ ∧ θ ≤ noiseNode R.grid.top 16 at hs
  have hc : BstLean.Part255.B (381958839397/800000000000) (71853017353/150000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry15W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry15C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply15 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨5,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨5,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨5,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum15W (by have := hn.1; omega),
    uniformNum15C (by have := hn.1; omega),
    fun _ hθ => (geometry15 hn R htop hθ).1,
    fun _ hθ => (geometry15 hn R htop hθ).2.1⟩

theorem geometry16 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨6,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 16 ≤ θ ∧ θ ≤ noiseNode R.grid.top 17 at hs
  have hc : BstLean.Part255.B (358958839397/750000000000) (1152501295001/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry16W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry16C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply16 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨6,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨6,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨6,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum16W (by have := hn.1; omega),
    uniformNum16C (by have := hn.1; omega),
    fun _ hθ => (geometry16 hn R htop hθ).1,
    fun _ hθ => (geometry16 hn R htop hθ).2.1⟩

theorem geometry17 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨7,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 17 ≤ θ ∧ θ ≤ noiseNode R.grid.top 18 at hs
  have hc : BstLean.Part255.B (5757300269749/12000000000000) (192559052059/400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry17W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry17C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply17 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨7,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨7,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨7,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum17W (by have := hn.1; omega),
    uniformNum17C (by have := hn.1; omega),
    fun _ hθ => (geometry17 hn R htop hθ).1,
    fun _ hθ => (geometry17 hn R htop hθ).2.1⟩

theorem geometry18 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨8,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 18 ≤ θ ∧ θ ≤ noiseNode R.grid.top 19 at hs
  have hc : BstLean.Part255.B (961876518191/2000000000000) (1158207329707/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry18W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry18C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply18 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨8,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨8,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨8,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum18W (by have := hn.1; omega),
    uniformNum18C (by have := hn.1; omega),
    fun _ hθ => (geometry18 hn R htop hθ).1,
    fun _ hθ => (geometry18 hn R htop hθ).2.1⟩

theorem geometry19 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨9,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 19 ≤ θ ∧ θ ≤ noiseNode R.grid.top 20 at hs
  have hc : BstLean.Part255.B (5785217948543/12000000000000) (58053017353/120000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry19W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry19C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply19 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨9,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨9,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨9,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum19W (by have := hn.1; omega),
    uniformNum19C (by have := hn.1; omega),
    fun _ hθ => (geometry19 hn R htop hθ).1,
    fun _ hθ => (geometry19 hn R htop hθ).2.1⟩

theorem geometry20 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨10,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 20 ≤ θ ∧ θ ≤ noiseNode R.grid.top 21 at hs
  have hc : BstLean.Part255.B (289958839397/600000000000) (387971121471/800000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry20W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry20C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply20 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨10,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨10,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨10,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum20W (by have := hn.1; omega),
    uniformNum20C (by have := hn.1; omega),
    fun _ hθ => (geometry20 hn R htop hθ).1,
    fun _ hθ => (geometry20 hn R htop hθ).2.1⟩

theorem geometry21 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨11,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 21 ≤ θ ∧ θ ≤ noiseNode R.grid.top 22 at hs
  have hc : BstLean.Part255.B (1937711875779/4000000000000) (583383190883/1200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry21W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry21C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply21 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨11,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨11,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨11,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum21W (by have := hn.1; omega),
    uniformNum21C (by have := hn.1; omega),
    fun _ hθ => (geometry21 hn R htop hθ).1,
    fun _ hθ => (geometry21 hn R htop hθ).2.1⟩

theorem geometry22 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨12,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 22 ≤ θ ∧ θ ≤ noiseNode R.grid.top 23 at hs
  have hc : BstLean.Part255.B (2913547233367/6000000000000) (1169619399119/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry22W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry22C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply22 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨12,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨12,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨12,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum22W (by have := hn.1; omega),
    uniformNum22C (by have := hn.1; omega),
    fun _ hθ => (geometry22 hn R htop hθ).1,
    fun _ hθ => (geometry22 hn R htop hθ).2.1⟩

theorem geometry23 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨13,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 23 ≤ θ ∧ θ ≤ noiseNode R.grid.top 24 at hs
  have hc : BstLean.Part255.B (5841053306131/12000000000000) (48853017353/100000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry23W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry23C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply23 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨13,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨13,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨13,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum23W (by have := hn.1; omega),
    uniformNum23C (by have := hn.1; omega),
    fun _ hθ => (geometry23 hn R htop hθ).1,
    fun _ hθ => (geometry23 hn R htop hθ).2.1⟩

theorem geometry24 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨14,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 24 ≤ θ ∧ θ ≤ noiseNode R.grid.top 25 at hs
  have hc : BstLean.Part255.B (243958839397/500000000000) (47013017353/96000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry24W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry24C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply24 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨14,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨14,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨14,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum24W (by have := hn.1; omega),
    uniformNum24C (by have := hn.1; omega),
    fun _ hθ => (geometry24 hn R htop hθ).1,
    fun _ hθ => (geometry24 hn R htop hθ).2.1⟩

theorem geometry25 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨15,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 25 ≤ θ ∧ θ ≤ noiseNode R.grid.top 26 at hs
  have hc : BstLean.Part255.B (234758839397/480000000000) (589089225589/1200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry25W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry25C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply25 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨15,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨15,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨15,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum25W (by have := hn.1; omega),
    uniformNum25C (by have := hn.1; omega),
    fun _ hθ => (geometry25 hn R htop hθ).1,
    fun _ hθ => (geometry25 hn R htop hθ).2.1⟩

theorem geometry26 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨16,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 26 ≤ θ ∧ θ ≤ noiseNode R.grid.top 27 at hs
  have hc : BstLean.Part255.B (2941464912161/6000000000000) (393677156177/800000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry26W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry26C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply26 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨16,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨16,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨16,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum26W (by have := hn.1; omega),
    uniformNum26C (by have := hn.1; omega),
    fun _ hθ => (geometry26 hn R htop hθ).1,
    fun _ hθ => (geometry26 hn R htop hθ).2.1⟩

theorem geometry27 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨17,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 27 ≤ θ ∧ θ ≤ noiseNode R.grid.top 28 at hs
  have hc : BstLean.Part255.B (1965629554573/4000000000000) (295971121471/600000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry27W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry27C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply27 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨17,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨17,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨17,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum27W (by have := hn.1; omega),
    uniformNum27C (by have := hn.1; omega),
    fun _ hθ => (geometry27 hn R htop hθ).1,
    fun _ hθ => (geometry27 hn R htop hθ).2.1⟩

theorem geometry28 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨18,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 28 ≤ θ ∧ θ ≤ noiseNode R.grid.top 29 at hs
  have hc : BstLean.Part255.B (1477711875779/3000000000000) (1186737503237/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry28W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry28C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply28 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨18,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨18,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨18,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum28W (by have := hn.1; omega),
    uniformNum28C (by have := hn.1; omega),
    fun _ hθ => (geometry28 hn R htop hθ).1,
    fun _ hθ => (geometry28 hn R htop hθ).2.1⟩

theorem geometry29 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨19,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 29 ≤ θ ∧ θ ≤ noiseNode R.grid.top 30 at hs
  have hc : BstLean.Part255.B (5924806342513/12000000000000) (39653017353/80000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry29W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry29C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply29 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨19,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨19,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨19,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum29W (by have := hn.1; omega),
    uniformNum29C (by have := hn.1; omega),
    fun _ hθ => (geometry29 hn R htop hθ).1,
    fun _ hθ => (geometry29 hn R htop hθ).2.1⟩

theorem geometry30 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨20,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 30 ≤ θ ∧ θ ≤ noiseNode R.grid.top 31 at hs
  have hc : BstLean.Part255.B (197958839397/400000000000) (1192443537943/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry30W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry30C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply30 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨20,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨20,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨20,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum30W (by have := hn.1; omega),
    uniformNum30C (by have := hn.1; omega),
    fun _ hθ => (geometry30 hn R htop hθ).1,
    fun _ hθ => (geometry30 hn R htop hθ).2.1⟩

theorem geometry31 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨21,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 31 ≤ θ ∧ θ ≤ noiseNode R.grid.top 32 at hs
  have hc : BstLean.Part255.B (5952724021307/12000000000000) (37353017353/75000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry31W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry31C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply31 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨21,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨21,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨21,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum31W (by have := hn.1; omega),
    uniformNum31C (by have := hn.1; omega),
    fun _ hθ => (geometry31 hn R htop hθ).1,
    fun _ hθ => (geometry31 hn R htop hθ).2.1⟩

theorem geometry32 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨22,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 32 ≤ θ ∧ θ ≤ noiseNode R.grid.top 33 at hs
  have hc : BstLean.Part255.B (186458839397/375000000000) (399383190883/800000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry32W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry32C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨22,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨22,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨22,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum32W (by have := hn.1; omega),
    uniformNum32C (by have := hn.1; omega),
    fun _ hθ => (geometry32 hn R htop hθ).1,
    fun _ hθ => (geometry32 hn R htop hθ).2.1⟩

theorem geometry33 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨23,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 33 ≤ θ ∧ θ ≤ noiseNode R.grid.top 34 at hs
  have hc : BstLean.Part255.B (1993547233367/4000000000000) (600501295001/1200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry33W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry33C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨23,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨23,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨23,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum33W (by have := hn.1; omega),
    uniformNum33C (by have := hn.1; omega),
    fun _ hθ => (geometry33 hn R htop hθ).1,
    fun _ hθ => (geometry33 hn R htop hθ).2.1⟩

theorem geometry34 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨24,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 34 ≤ θ ∧ θ ≤ noiseNode R.grid.top 35 at hs
  have hc : BstLean.Part255.B (2997300269749/6000000000000) (240771121471/480000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry34W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry34C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨24,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨24,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨24,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum34W (by have := hn.1; omega),
    uniformNum34C (by have := hn.1; omega),
    fun _ hθ => (geometry34 hn R htop hθ).1,
    fun _ hθ => (geometry34 hn R htop hθ).2.1⟩

theorem geometry35 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨25,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 35 ≤ θ ∧ θ ≤ noiseNode R.grid.top 36 at hs
  have hc : BstLean.Part255.B (1201711875779/2400000000000) (100559052059/200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry35W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry35C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨25,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨25,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨25,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum35W (by have := hn.1; omega),
    uniformNum35C (by have := hn.1; omega),
    fun _ hθ => (geometry35 hn R htop hθ).1,
    fun _ hθ => (geometry35 hn R htop hθ).2.1⟩

theorem geometry36 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨26,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 36 ≤ θ ∧ θ ≤ noiseNode R.grid.top 37 at hs
  have hc : BstLean.Part255.B (501876518191/1000000000000) (1209561642061/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry36W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry36C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨26,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨26,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨26,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum36W (by have := hn.1; omega),
    uniformNum36C (by have := hn.1; omega),
    fun _ hθ => (geometry36 hn R htop hθ).1,
    fun _ hθ => (geometry36 hn R htop hθ).2.1⟩

theorem geometry37 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨27,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 37 ≤ θ ∧ θ ≤ noiseNode R.grid.top 38 at hs
  have hc : BstLean.Part255.B (6036477057689/12000000000000) (606207329707/1200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry37W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry37C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨27,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨27,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨27,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum37W (by have := hn.1; omega),
    uniformNum37C (by have := hn.1; omega),
    fun _ hθ => (geometry37 hn R htop hθ).1,
    fun _ hθ => (geometry37 hn R htop hθ).2.1⟩

theorem geometry38 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨28,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 38 ≤ θ ∧ θ ≤ noiseNode R.grid.top 39 at hs
  have hc : BstLean.Part255.B (3025217948543/6000000000000) (405089225589/800000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry38W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry38C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨28,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨28,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨28,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum38W (by have := hn.1; omega),
    uniformNum38C (by have := hn.1; omega),
    fun _ hθ => (geometry38 hn R htop hθ).1,
    fun _ hθ => (geometry38 hn R htop hθ).2.1⟩

theorem geometry39 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨29,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 39 ≤ θ ∧ θ ≤ noiseNode R.grid.top 40 at hs
  have hc : BstLean.Part255.B (2021464912161/4000000000000) (30453017353/60000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry39W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry39C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨29,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨29,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨29,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum39W (by have := hn.1; omega),
    uniformNum39C (by have := hn.1; omega),
    fun _ hθ => (geometry39 hn R htop hθ).1,
    fun _ hθ => (geometry39 hn R htop hθ).2.1⟩

theorem geometry40 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨30,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 40 ≤ θ ∧ θ ≤ noiseNode R.grid.top 41 at hs
  have hc : BstLean.Part255.B (151958839397/300000000000) (1220973711473/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry40W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry40C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨30,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨30,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨30,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum40W (by have := hn.1; omega),
    uniformNum40C (by have := hn.1; omega),
    fun _ hθ => (geometry40 hn R htop hθ).1,
    fun _ hθ => (geometry40 hn R htop hθ).2.1⟩

theorem geometry41 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨31,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 41 ≤ θ ∧ θ ≤ noiseNode R.grid.top 42 at hs
  have hc : BstLean.Part255.B (6092312415277/12000000000000) (203971121471/400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry41W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry41C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨31,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨31,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨31,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum41W (by have := hn.1; omega),
    uniformNum41C (by have := hn.1; omega),
    fun _ hθ => (geometry41 hn R htop hθ).1,
    fun _ hθ => (geometry41 hn R htop hθ).2.1⟩

theorem geometry42 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨32,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 42 ≤ θ ∧ θ ≤ noiseNode R.grid.top 43 at hs
  have hc : BstLean.Part255.B (1017711875779/2000000000000) (1226679746179/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry42W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry42C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨32,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨32,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨32,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum42W (by have := hn.1; omega),
    uniformNum42C (by have := hn.1; omega),
    fun _ hθ => (geometry42 hn R htop hθ).1,
    fun _ hθ => (geometry42 hn R htop hθ).2.1⟩

theorem geometry43 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨33,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 43 ≤ θ ∧ θ ≤ noiseNode R.grid.top 44 at hs
  have hc : BstLean.Part255.B (6120230094071/12000000000000) (307383190883/600000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry43W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry43C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨33,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨33,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨33,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum43W (by have := hn.1; omega),
    uniformNum43C (by have := hn.1; omega),
    fun _ hθ => (geometry43 hn R htop hθ).1,
    fun _ hθ => (geometry43 hn R htop hθ).2.1⟩

theorem geometry44 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨34,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 44 ≤ θ ∧ θ ≤ noiseNode R.grid.top 45 at hs
  have hc : BstLean.Part255.B (1533547233367/3000000000000) (82159052059/160000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry44W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry44C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨34,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨34,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨34,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum44W (by have := hn.1; omega),
    uniformNum44C (by have := hn.1; omega),
    fun _ hθ => (geometry44 hn R htop hθ).1,
    fun _ hθ => (geometry44 hn R htop hθ).2.1⟩

theorem geometry45 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨35,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 45 ≤ θ ∧ θ ≤ noiseNode R.grid.top 46 at hs
  have hc : BstLean.Part255.B (409876518191/800000000000) (617619399119/1200000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry45W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry45C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨35,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨35,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨35,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum45W (by have := hn.1; omega),
    uniformNum45C (by have := hn.1; omega),
    fun _ hθ => (geometry45 hn R htop hθ).1,
    fun _ hθ => (geometry45 hn R htop hθ).2.1⟩

theorem geometry46 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨36,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 46 ≤ θ ∧ θ ≤ noiseNode R.grid.top 47 at hs
  have hc : BstLean.Part255.B (3081053306131/6000000000000) (1238091815591/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry46W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry46C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨36,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨36,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨36,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum46W (by have := hn.1; omega),
    uniformNum46C (by have := hn.1; omega),
    fun _ hθ => (geometry46 hn R htop hθ).1,
    fun _ hθ => (geometry46 hn R htop hθ).2.1⟩

theorem geometry47 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨37,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 47 ≤ θ ∧ θ ≤ noiseNode R.grid.top 48 at hs
  have hc : BstLean.Part255.B (6176065451659/12000000000000) (25853017353/50000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry47W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry47C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨37,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨37,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨37,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum47W (by have := hn.1; omega),
    uniformNum47C (by have := hn.1; omega),
    fun _ hθ => (geometry47 hn R htop hθ).1,
    fun _ hθ => (geometry47 hn R htop hθ).2.1⟩

theorem geometry48 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨38,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 48 ≤ θ ∧ θ ≤ noiseNode R.grid.top 49 at hs
  have hc : BstLean.Part255.B (128958839397/250000000000) (1243797850297/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry48W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry48C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨38,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨38,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨38,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum48W (by have := hn.1; omega),
    uniformNum48C (by have := hn.1; omega),
    fun _ hθ => (geometry48 hn R htop hθ).1,
    fun _ hθ => (geometry48 hn R htop hθ).2.1⟩

theorem geometry49 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨39,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 49 ≤ θ ∧ θ ≤ noiseNode R.grid.top 50 at hs
  have hc : BstLean.Part255.B (6203983130453/12000000000000) (24933017353/48000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry49W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry49C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨39,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨39,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨39,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum49W (by have := hn.1; omega),
    uniformNum49C (by have := hn.1; omega),
    fun _ hθ => (geometry49 hn R htop hθ).1,
    fun _ hθ => (geometry49 hn R htop hθ).2.1⟩

theorem geometry50 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨40,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 50 ≤ θ ∧ θ ≤ noiseNode R.grid.top 51 at hs
  have hc : BstLean.Part255.B (124358839397/240000000000) (416501295001/800000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry50W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry50C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨40,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨40,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨40,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum50W (by have := hn.1; omega),
    uniformNum50C (by have := hn.1; omega),
    fun _ hθ => (geometry50 hn R htop hθ).1,
    fun _ hθ => (geometry50 hn R htop hθ).2.1⟩

theorem geometry51 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨41,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 51 ≤ θ ∧ θ ≤ noiseNode R.grid.top 52 at hs
  have hc : BstLean.Part255.B (2077300269749/4000000000000) (313089225589/600000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry51W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry51C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨41,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨41,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨41,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum51W (by have := hn.1; omega),
    uniformNum51C (by have := hn.1; omega),
    fun _ hθ => (geometry51 hn R htop hθ).1,
    fun _ hθ => (geometry51 hn R htop hθ).2.1⟩

theorem geometry52 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) {θ : ℝ}
    (hθ : θ ∈ cell R.grid (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleWide (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard n θ BstLean.Part199.exampleCore (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters ⟨42,by decide⟩).cRadius := by
  have hs := cell_source hθ
  change noiseNode R.grid.top 52 ≤ θ ∧ θ ≤ noiseNode R.grid.top 53 at hs
  have hc : BstLean.Part255.B (1561464912161/3000000000000) (1255209919709/2400000000000) θ := by
    norm_num [BstLean.Part255.B, noiseNode] at hs ⊢
    constructor <;> linarith only [hs.1,hs.2,htop.1,htop.2]
  have hw := BstLean.Part271.R4.SharedGeometry.geometry52W hn hc
  have hk := BstLean.Part271.R4.SharedGeometry.geometry52C hn hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) : Supply n (parameters ⟨42,by decide⟩)
    (cellLower R.grid (sourceIndex ⟨42,by decide⟩))
    (cellUpper R.grid (sourceIndex ⟨42,by decide⟩)) :=
  ⟨parameters_valid _, uniformNum52W (by have := hn.1; omega),
    uniformNum52C (by have := hn.1; omega),
    fun _ hθ => (geometry52 hn R htop hθ).1,
    fun _ hθ => (geometry52 hn R htop hθ).2.1⟩

theorem supplies {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) (j : Fin 43) :
    Supply n (parameters j) (cellLower R.grid (sourceIndex j)) (cellUpper R.grid (sourceIndex j)) := by
  match j with
  | ⟨0,_⟩ => exact supply10 hn R htop
  | ⟨1,_⟩ => exact supply11 hn R htop
  | ⟨2,_⟩ => exact supply12 hn R htop
  | ⟨3,_⟩ => exact supply13 hn R htop
  | ⟨4,_⟩ => exact supply14 hn R htop
  | ⟨5,_⟩ => exact supply15 hn R htop
  | ⟨6,_⟩ => exact supply16 hn R htop
  | ⟨7,_⟩ => exact supply17 hn R htop
  | ⟨8,_⟩ => exact supply18 hn R htop
  | ⟨9,_⟩ => exact supply19 hn R htop
  | ⟨10,_⟩ => exact supply20 hn R htop
  | ⟨11,_⟩ => exact supply21 hn R htop
  | ⟨12,_⟩ => exact supply22 hn R htop
  | ⟨13,_⟩ => exact supply23 hn R htop
  | ⟨14,_⟩ => exact supply24 hn R htop
  | ⟨15,_⟩ => exact supply25 hn R htop
  | ⟨16,_⟩ => exact supply26 hn R htop
  | ⟨17,_⟩ => exact supply27 hn R htop
  | ⟨18,_⟩ => exact supply28 hn R htop
  | ⟨19,_⟩ => exact supply29 hn R htop
  | ⟨20,_⟩ => exact supply30 hn R htop
  | ⟨21,_⟩ => exact supply31 hn R htop
  | ⟨22,_⟩ => exact supply32 hn R htop
  | ⟨23,_⟩ => exact supply33 hn R htop
  | ⟨24,_⟩ => exact supply34 hn R htop
  | ⟨25,_⟩ => exact supply35 hn R htop
  | ⟨26,_⟩ => exact supply36 hn R htop
  | ⟨27,_⟩ => exact supply37 hn R htop
  | ⟨28,_⟩ => exact supply38 hn R htop
  | ⟨29,_⟩ => exact supply39 hn R htop
  | ⟨30,_⟩ => exact supply40 hn R htop
  | ⟨31,_⟩ => exact supply41 hn R htop
  | ⟨32,_⟩ => exact supply42 hn R htop
  | ⟨33,_⟩ => exact supply43 hn R htop
  | ⟨34,_⟩ => exact supply44 hn R htop
  | ⟨35,_⟩ => exact supply45 hn R htop
  | ⟨36,_⟩ => exact supply46 hn R htop
  | ⟨37,_⟩ => exact supply47 hn R htop
  | ⟨38,_⟩ => exact supply48 hn R htop
  | ⟨39,_⟩ => exact supply49 hn R htop
  | ⟨40,_⟩ => exact supply50 hn R htop
  | ⟨41,_⟩ => exact supply51 hn R htop
  | ⟨42,_⟩ => exact supply52 hn R htop
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem radii {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) (j : Fin 43) {θ : ℝ} (hθ : θ ∈ cell R.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus n θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius := by
  match j with
  | ⟨0,_⟩ => exact (geometry10 hn R htop hθ).2.2
  | ⟨1,_⟩ => exact (geometry11 hn R htop hθ).2.2
  | ⟨2,_⟩ => exact (geometry12 hn R htop hθ).2.2
  | ⟨3,_⟩ => exact (geometry13 hn R htop hθ).2.2
  | ⟨4,_⟩ => exact (geometry14 hn R htop hθ).2.2
  | ⟨5,_⟩ => exact (geometry15 hn R htop hθ).2.2
  | ⟨6,_⟩ => exact (geometry16 hn R htop hθ).2.2
  | ⟨7,_⟩ => exact (geometry17 hn R htop hθ).2.2
  | ⟨8,_⟩ => exact (geometry18 hn R htop hθ).2.2
  | ⟨9,_⟩ => exact (geometry19 hn R htop hθ).2.2
  | ⟨10,_⟩ => exact (geometry20 hn R htop hθ).2.2
  | ⟨11,_⟩ => exact (geometry21 hn R htop hθ).2.2
  | ⟨12,_⟩ => exact (geometry22 hn R htop hθ).2.2
  | ⟨13,_⟩ => exact (geometry23 hn R htop hθ).2.2
  | ⟨14,_⟩ => exact (geometry24 hn R htop hθ).2.2
  | ⟨15,_⟩ => exact (geometry25 hn R htop hθ).2.2
  | ⟨16,_⟩ => exact (geometry26 hn R htop hθ).2.2
  | ⟨17,_⟩ => exact (geometry27 hn R htop hθ).2.2
  | ⟨18,_⟩ => exact (geometry28 hn R htop hθ).2.2
  | ⟨19,_⟩ => exact (geometry29 hn R htop hθ).2.2
  | ⟨20,_⟩ => exact (geometry30 hn R htop hθ).2.2
  | ⟨21,_⟩ => exact (geometry31 hn R htop hθ).2.2
  | ⟨22,_⟩ => exact (geometry32 hn R htop hθ).2.2
  | ⟨23,_⟩ => exact (geometry33 hn R htop hθ).2.2
  | ⟨24,_⟩ => exact (geometry34 hn R htop hθ).2.2
  | ⟨25,_⟩ => exact (geometry35 hn R htop hθ).2.2
  | ⟨26,_⟩ => exact (geometry36 hn R htop hθ).2.2
  | ⟨27,_⟩ => exact (geometry37 hn R htop hθ).2.2
  | ⟨28,_⟩ => exact (geometry38 hn R htop hθ).2.2
  | ⟨29,_⟩ => exact (geometry39 hn R htop hθ).2.2
  | ⟨30,_⟩ => exact (geometry40 hn R htop hθ).2.2
  | ⟨31,_⟩ => exact (geometry41 hn R htop hθ).2.2
  | ⟨32,_⟩ => exact (geometry42 hn R htop hθ).2.2
  | ⟨33,_⟩ => exact (geometry43 hn R htop hθ).2.2
  | ⟨34,_⟩ => exact (geometry44 hn R htop hθ).2.2
  | ⟨35,_⟩ => exact (geometry45 hn R htop hθ).2.2
  | ⟨36,_⟩ => exact (geometry46 hn R htop hθ).2.2
  | ⟨37,_⟩ => exact (geometry47 hn R htop hθ).2.2
  | ⟨38,_⟩ => exact (geometry48 hn R htop hθ).2.2
  | ⟨39,_⟩ => exact (geometry49 hn R htop hθ).2.2
  | ⟨40,_⟩ => exact (geometry50 hn R htop hθ).2.2
  | ⟨41,_⟩ => exact (geometry51 hn R htop hθ).2.2
  | ⟨42,_⟩ => exact (geometry52 hn R htop hθ).2.2
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def covarianceInputs {n : ℕ} (hn : n ∈ Icc 13225 16199) (R : ScalarRow n)
    (htop : R.grid.top ∈ Icc (105958839397/200000000000) (21253017353/40000000000)) (A : FrameRepair n R) :
    CovarianceInputs n R.grid parameters (caps A) :=
  covarianceInputs_from_supplies (by have := hn.1; omega) A
    (supplies hn R htop) (fun j _ hθ => radii hn R htop j hθ)

end BstLean.Part271.R4.SharedCovariance
