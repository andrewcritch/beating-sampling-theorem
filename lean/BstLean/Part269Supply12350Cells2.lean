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
theorem geometryCell20 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨10,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨10,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry20W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (96791053463421902878493/200000000000000000000000) (97031730432291150984463/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry20C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (96791053463421902878493/200000000000000000000000) (97031730432291150984463/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply20 : Supply 12350 (parameters ⟨10,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨10,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨10,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum20W (by norm_num),uniformNum20C (by norm_num),
    fun _ hθ => (geometryCell20 hθ).1,fun _ hθ => (geometryCell20 hθ).2.1⟩

theorem geometryCell21 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨11,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨11,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry21W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (60644128835370623764011/125000000000000000000000) (243178341608381585911689/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry21C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (60644128835370623764011/125000000000000000000000) (243178341608381585911689/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply21 : Supply 12350 (parameters ⟨11,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨11,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨11,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum21W (by norm_num),uniformNum21C (by norm_num),
    fun _ hθ => (geometryCell21 hθ).1,fun _ hθ => (geometryCell21 hθ).2.1⟩

theorem geometryCell22 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨12,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨12,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry22W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (15198462314025639557241/31250000000000000000000) (487554714272070588724441/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry22C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (15198462314025639557241/31250000000000000000000) (487554714272070588724441/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply22 : Supply 12350 (parameters ⟨12,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨12,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨12,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum22W (by norm_num),uniformNum22C (by norm_num),
    fun _ hθ => (geometryCell22 hθ).1,fun _ hθ => (geometryCell22 hθ).2.1⟩

theorem geometryCell23 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨13,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨13,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry23W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (97509711482935188310267/200000000000000000000000) (488752745327378005625503/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry23C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (97509711482935188310267/200000000000000000000000) (488752745327378005625503/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply23 : Supply 12350 (parameters ⟨13,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨13,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨13,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum23W (by norm_num),uniformNum23C (by norm_num),
    fun _ hθ => (geometryCell23 hθ).1,fun _ hθ => (geometryCell23 hθ).2.1⟩

theorem geometryCell24 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨14,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨14,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry24W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (244373160390265708635479/500000000000000000000000) (244975388191342711263283/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry24C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (244373160390265708635479/500000000000000000000000) (244975388191342711263283/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply24 : Supply 12350 (parameters ⟨14,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨14,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨14,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum24W (by norm_num),uniformNum24C (by norm_num),
    fun _ hθ => (geometryCell24 hθ).1,fun _ hθ => (geometryCell24 hθ).2.1⟩


end BstLean.Part269.N12350
