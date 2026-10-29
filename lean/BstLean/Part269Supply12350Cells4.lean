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
theorem geometryCell30 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨20,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨20,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry30W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (247966450487832135794349/500000000000000000000000) (248569481357264961966471/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry30C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (247966450487832135794349/500000000000000000000000) (248569481357264961966471/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply30 : Supply 12350 (parameters ⟨20,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨20,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨20,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum30W (by norm_num),uniformNum30C (by norm_num),
    fun _ hθ => (geometryCell30 hθ).1,fun _ hθ => (geometryCell30 hθ).2.1⟩

theorem geometryCell31 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨21,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨21,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry31W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (497130664341519747308321/1000000000000000000000000) (124584248442459335208501/250000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry31C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (497130664341519747308321/1000000000000000000000000) (124584248442459335208501/250000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply31 : Supply 12350 (parameters ⟨21,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨21,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨21,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum31W (by norm_num),uniformNum31C (by norm_num),
    fun _ hθ => (geometryCell31 hθ).1,fun _ hθ => (geometryCell31 hθ).2.1⟩

theorem geometryCell32 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨22,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨22,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry32W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (99665685541475044605589/200000000000000000000000) (499535024825144757735067/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry32C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (99665685541475044605589/200000000000000000000000) (499535024825144757735067/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 : Supply 12350 (parameters ⟨22,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨22,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨22,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum32W (by norm_num),uniformNum32C (by norm_num),
    fun _ hθ => (geometryCell32 hθ).1,fun _ hθ => (geometryCell32 hθ).2.1⟩

theorem geometryCell33 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨23,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨23,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry33W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (31220386942076918671723/62500000000000000000000) (500733055880452174636129/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry33C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (31220386942076918671723/62500000000000000000000) (500733055880452174636129/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 : Supply 12350 (parameters ⟨23,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨23,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨23,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum33W (by norm_num),uniformNum33C (by norm_num),
    fun _ hθ => (geometryCell33 hθ).1,fun _ hθ => (geometryCell33 hθ).2.1⟩

theorem geometryCell34 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨24,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨24,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry34W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (500723954439086174467191/1000000000000000000000000) (62741385866969948942149/125000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry34C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (500723954439086174467191/1000000000000000000000000) (62741385866969948942149/125000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 : Supply 12350 (parameters ⟨24,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨24,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨24,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum34W (by norm_num),uniformNum34C (by norm_num),
    fun _ hθ => (geometryCell34 hθ).1,fun _ hθ => (geometryCell34 hθ).2.1⟩


end BstLean.Part269.N12350
