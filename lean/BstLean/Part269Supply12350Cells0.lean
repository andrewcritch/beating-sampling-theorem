import BstLean.Part269Row12350
import BstLean.Part269Geometry0_0
import BstLean.Part269Geometry0_1
import BstLean.Part264bUniformTI
namespace BstLean.Part269.N12350
open Real Set MeasureTheory BstLean.Part264b BstLean.Part269
open BstLean.Part130 BstLean.Part157 BstLean.Part159 BstLean.Part160 BstLean.Part169
open BstLean.Part255 (parameters parameters_valid sourceIndex)
open BstLean.Part263 (Supply cell cellLower cellUpper)
open BstLean.Part264b
theorem geometryCell10 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨0,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨0,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry10W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (58997204207319344649529/125000000000000000000000) (473178341608381585911689/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry10C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (58997204207319344649529/125000000000000000000000) (473178341608381585911689/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply10 : Supply 12350 (parameters ⟨0,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨0,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨0,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum10W (by norm_num),uniformNum10C (by norm_num),
    fun _ hθ => (geometryCell10 hθ).1,fun _ hθ => (geometryCell10 hθ).2.1⟩

theorem geometryCell11 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨1,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨1,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry11W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (29573462314025639557241/62500000000000000000000) (29648523291480562675797/62500000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry11C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (29573462314025639557241/62500000000000000000000) (29648523291480562675797/62500000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply11 : Supply 12350 (parameters ⟨1,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨1,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨1,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum11W (by norm_num),uniformNum11C (by norm_num),
    fun _ hθ => (geometryCell11 hθ).1,fun _ hθ => (geometryCell11 hθ).2.1⟩

theorem geometryCell12 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨2,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨2,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry12W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (474373160390265708635479/1000000000000000000000000) (95114880743799283942763/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry12C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (474373160390265708635479/1000000000000000000000000) (95114880743799283942763/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply12 : Supply 12350 (parameters ⟨2,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨2,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨2,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum12W (by norm_num),uniformNum12C (by norm_num),
    fun _ hθ => (geometryCell12 hθ).1,fun _ hθ => (geometryCell12 hθ).2.1⟩

theorem geometryCell13 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨3,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨3,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry13W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (237785461878060592177551/500000000000000000000000) (476772434774303836614877/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry13C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (237785461878060592177551/500000000000000000000000) (476772434774303836614877/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply13 : Supply 12350 (parameters ⟨3,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨3,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨3,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum13W (by norm_num),uniformNum13C (by norm_num),
    fun _ hθ => (geometryCell13 hθ).1,fun _ hθ => (geometryCell13 hθ).2.1⟩

theorem geometryCell14 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨4,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨4,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry14W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (19070747484879066402989/40000000000000000000000) (23898523291480562675797/50000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry14C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (19070747484879066402989/40000000000000000000000) (23898523291480562675797/50000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply14 : Supply 12350 (parameters ⟨4,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨4,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨4,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum14W (by norm_num),uniformNum14C (by norm_num),
    fun _ hθ => (geometryCell14 hθ).1,fun _ hθ => (geometryCell14 hθ).2.1⟩


end BstLean.Part269.N12350
