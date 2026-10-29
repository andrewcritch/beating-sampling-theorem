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
theorem geometryCell40 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨30,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨30,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry40W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (507910534634219028784931/1000000000000000000000000) (31819954579225255808973/62500000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry40C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (507910534634219028784931/1000000000000000000000000) (31819954579225255808973/62500000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 : Supply 12350 (parameters ⟨30,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨30,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨30,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum40W (by norm_num),uniformNum40C (by norm_num),
    fun _ hθ => (geometryCell40 hθ).1,fun _ hθ => (geometryCell40 hθ).2.1⟩

theorem geometryCell41 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨31,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨31,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry41W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (254554149000037252252277/500000000000000000000000) (51031730432291150984463/100000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry41C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (254554149000037252252277/500000000000000000000000) (51031730432291150984463/100000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 : Supply 12350 (parameters ⟨31,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨31,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨31,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum41W (by norm_num),uniformNum41C (by norm_num),
    fun _ hθ => (geometryCell41 hθ).1,fun _ hθ => (geometryCell41 hθ).2.1⟩

theorem geometryCell42 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨32,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨32,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry42W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (510306061365929980224177/1000000000000000000000000) (511515335378218926745693/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry42C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (510306061365929980224177/1000000000000000000000000) (511515335378218926745693/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 : Supply 12350 (parameters ⟨32,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨32,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨32,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum42W (by norm_num),uniformNum42C (by norm_num),
    fun _ hθ => (geometryCell42 hθ).1,fun _ hθ => (geometryCell42 hθ).2.1⟩

theorem geometryCell43 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨33,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨33,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry43W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (511503824731785455943801/1000000000000000000000000) (128178341608381585911689/250000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry43C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (511503824731785455943801/1000000000000000000000000) (128178341608381585911689/250000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 : Supply 12350 (parameters ⟨33,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨33,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨33,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum43W (by norm_num),uniformNum43C (by norm_num),
    fun _ hθ => (geometryCell43 hθ).1,fun _ hθ => (geometryCell43 hθ).2.1⟩

theorem geometryCell44 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨34,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨34,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry44W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (8010962314025639557241/15625000000000000000000) (256955698744416880273909/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry44C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (8010962314025639557241/15625000000000000000000) (256955698744416880273909/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 : Supply 12350 (parameters ⟨34,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨34,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨34,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum44W (by norm_num),uniformNum44C (by norm_num),
    fun _ hθ => (geometryCell44 hθ).1,fun _ hθ => (geometryCell44 hθ).2.1⟩


end BstLean.Part269.N12350
