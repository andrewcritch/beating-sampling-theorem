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
theorem geometryCell25 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨15,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨15,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry25W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (244972042073193446495291/500000000000000000000000) (491148807437992839427629/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry25C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (244972042073193446495291/500000000000000000000000) (491148807437992839427629/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply25 : Supply 12350 (parameters ⟨15,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨15,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨15,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum25W (by norm_num),uniformNum25C (by norm_num),
    fun _ hθ => (geometryCell25 hθ).1,fun _ hθ => (geometryCell25 hθ).2.1⟩

theorem geometryCell26 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨16,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨16,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry26W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (98228369502448473742041/200000000000000000000000) (492346838493300256328691/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry26C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (98228369502448473742041/200000000000000000000000) (492346838493300256328691/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply26 : Supply 12350 (parameters ⟨16,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨16,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨16,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum26W (by norm_num),uniformNum26C (by norm_num),
    fun _ hθ => (geometryCell26 hθ).1,fun _ hθ => (geometryCell26 hθ).2.1⟩

theorem geometryCell27 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨17,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨17,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry27W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (123084902719524461107457/250000000000000000000000) (246772434774303836614877/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry27C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (123084902719524461107457/250000000000000000000000) (246772434774303836614877/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply27 : Supply 12350 (parameters ⟨17,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨17,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨17,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum27W (by norm_num),uniformNum27C (by norm_num),
    fun _ hθ => (geometryCell27 hθ).1,fun _ hθ => (geometryCell27 hθ).2.1⟩

theorem geometryCell28 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨18,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨18,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry28W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (493537374243953320149451/1000000000000000000000000) (3865178910968086641647/7812500000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry28C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (493537374243953320149451/1000000000000000000000000) (3865178910968086641647/7812500000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply28 : Supply 12350 (parameters ⟨18,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨18,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨18,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum28W (by norm_num),uniformNum28C (by norm_num),
    fun _ hθ => (geometryCell28 hθ).1,fun _ hθ => (geometryCell28 hθ).2.1⟩

theorem geometryCell29 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨19,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨19,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry29W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (19789405504392351834763/40000000000000000000000) (495940931659222507031879/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry29C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (19789405504392351834763/40000000000000000000000) (495940931659222507031879/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply29 : Supply 12350 (parameters ⟨19,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨19,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨19,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum29W (by norm_num),uniformNum29C (by norm_num),
    fun _ hθ => (geometryCell29 hθ).1,fun _ hθ => (geometryCell29 hθ).2.1⟩


end BstLean.Part269.N12350
