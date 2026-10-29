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
theorem geometryCell50 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨40,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨40,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry50W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (129972042073193446495291/250000000000000000000000) (260549791910339130977097/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry50C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (129972042073193446495291/250000000000000000000000) (260549791910339130977097/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 : Supply 12350 (parameters ⟨40,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨40,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨40,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum50W (by norm_num),uniformNum50C (by norm_num),
    fun _ hθ => (geometryCell50 hθ).1,fun _ hθ => (geometryCell50 hθ).2.1⟩

theorem geometryCell51 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨41,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨41,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry51W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (521085931658629261700787/1000000000000000000000000) (522297614875985678855257/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry51C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (521085931658629261700787/1000000000000000000000000) (522297614875985678855257/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 : Supply 12350 (parameters ⟨41,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨41,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨41,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum51W (by norm_num),uniformNum51C (by norm_num),
    fun _ hθ => (geometryCell51 hθ).1,fun _ hθ => (geometryCell51 hθ).2.1⟩

theorem geometryCell52 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨42,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨42,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry52W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (52228369502448473742041/100000000000000000000000) (523495645931293095756319/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry52C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (52228369502448473742041/100000000000000000000000) (523495645931293095756319/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 : Supply 12350 (parameters ⟨42,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨42,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨42,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum52W (by norm_num),uniformNum52C (by norm_num),
    fun _ hθ => (geometryCell52 hθ).1,fun _ hθ => (geometryCell52 hθ).2.1⟩


end BstLean.Part269.N12350
