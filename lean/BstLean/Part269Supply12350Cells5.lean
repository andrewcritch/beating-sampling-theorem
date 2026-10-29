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
theorem geometryCell35 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨25,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨25,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry35W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (250960858902470825093407/500000000000000000000000) (100625823598213401687651/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry35C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (250960858902470825093407/500000000000000000000000) (100625823598213401687651/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 : Supply 12350 (parameters ⟨25,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨25,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨25,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum35W (by norm_num),uniformNum35C (by norm_num),
    fun _ hθ => (geometryCell35 hθ).1,fun _ hθ => (geometryCell35 hθ).2.1⟩

theorem geometryCell36 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨26,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨26,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry36W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (251559740585398562953219/500000000000000000000000) (504327149046374425339317/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry36C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (251559740585398562953219/500000000000000000000000) (504327149046374425339317/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 : Supply 12350 (parameters ⟨26,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨26,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨26,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum36W (by norm_num),uniformNum36C (by norm_num),
    fun _ hθ => (geometryCell36 hθ).1,fun _ hθ => (geometryCell36 hθ).2.1⟩

theorem geometryCell37 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨27,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨27,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry37W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (504317244536652601626061/1000000000000000000000000) (25276259005084092112019/50000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry37C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (504317244536652601626061/1000000000000000000000000) (25276259005084092112019/50000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 : Supply 12350 (parameters ⟨27,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨27,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨27,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum37W (by norm_num),uniformNum37C (by norm_num),
    fun _ hθ => (geometryCell37 hθ).1,fun _ hθ => (geometryCell37 hθ).2.1⟩

theorem geometryCell38 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨28,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨28,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry38W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (126378751975627019336421/250000000000000000000000) (506723211156989259141443/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry38C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (126378751975627019336421/250000000000000000000000) (506723211156989259141443/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 : Supply 12350 (parameters ⟨28,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨28,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨28,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum38W (by norm_num),uniformNum38C (by norm_num),
    fun _ hθ => (geometryCell38 hθ).1,fun _ hθ => (geometryCell38 hθ).2.1⟩

theorem geometryCell39 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨29,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨29,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry39W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (126678192817090888266327/250000000000000000000000) (101584248442459335208501/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry39C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (126678192817090888266327/250000000000000000000000) (101584248442459335208501/200000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 : Supply 12350 (parameters ⟨29,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨29,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨29,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum39W (by norm_num),uniformNum39C (by norm_num),
    fun _ hθ => (geometryCell39 hθ).1,fun _ hθ => (geometryCell39 hθ).2.1⟩


end BstLean.Part269.N12350
