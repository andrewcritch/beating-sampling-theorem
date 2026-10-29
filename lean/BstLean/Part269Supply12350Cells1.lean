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
theorem geometryCell15 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨5,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨5,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry15W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (477966450487832135794349/1000000000000000000000000) (239584248442459335208501/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry15C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (477966450487832135794349/1000000000000000000000000) (239584248442459335208501/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply15 : Supply 12350 (parameters ⟨5,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨5,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨5,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum15W (by norm_num),uniformNum15C (by norm_num),
    fun _ hθ => (geometryCell15 hθ).1,fun _ hθ => (geometryCell15 hθ).2.1⟩

theorem geometryCell16 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨6,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨6,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry16W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (119791053463421902878493/250000000000000000000000) (96073305588045217463613/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry16C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (119791053463421902878493/250000000000000000000000) (96073305588045217463613/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply16 : Supply 12350 (parameters ⟨6,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨6,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨6,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum16W (by norm_num),uniformNum16C (by norm_num),
    fun _ hθ => (geometryCell16 hθ).1,fun _ hθ => (geometryCell16 hθ).2.1⟩

theorem geometryCell17 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨7,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨7,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry17W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (96072395443908617446719/200000000000000000000000) (60195569874441688027391/125000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry17C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (96072395443908617446719/200000000000000000000000) (60195569874441688027391/125000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply17 : Supply 12350 (parameters ⟨7,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨7,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨7,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum17W (by norm_num),uniformNum17C (by norm_num),
    fun _ hθ => (geometryCell17 hθ).1,fun _ hθ => (geometryCell17 hθ).2.1⟩

theorem geometryCell18 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨8,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨8,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry18W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (481559740585398562953219/1000000000000000000000000) (48276259005084092112019/100000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry18C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (481559740585398562953219/1000000000000000000000000) (48276259005084092112019/100000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply18 : Supply 12350 (parameters ⟨8,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨8,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨8,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum18W (by norm_num),uniformNum18C (by norm_num),
    fun _ hθ => (geometryCell18 hθ).1,fun _ hθ => (geometryCell18 hθ).2.1⟩

theorem geometryCell19 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨9,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨9,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry19W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (241378751975627019336421/500000000000000000000000) (483960621106148338021253/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry19C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (241378751975627019336421/500000000000000000000000) (483960621106148338021253/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply19 : Supply 12350 (parameters ⟨9,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨9,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨9,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum19W (by norm_num),uniformNum19C (by norm_num),
    fun _ hθ => (geometryCell19 hθ).1,fun _ hθ => (geometryCell19 hθ).2.1⟩


end BstLean.Part269.N12350
