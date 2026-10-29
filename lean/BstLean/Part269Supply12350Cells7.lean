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
theorem geometryCell45 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨35,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨35,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry45W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (513899351463496407383047/1000000000000000000000000) (515109428544141177448881/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry45C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (513899351463496407383047/1000000000000000000000000) (515109428544141177448881/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 : Supply 12350 (parameters ⟨35,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨35,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨35,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum45W (by norm_num),uniformNum45C (by norm_num),
    fun _ hθ => (geometryCell45 hθ).1,fun _ hθ => (geometryCell45 hθ).2.1⟩

theorem geometryCell46 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨36,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨36,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry46W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (515097114829351883102671/1000000000000000000000000) (516307459599448594349943/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry46C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (515097114829351883102671/1000000000000000000000000) (516307459599448594349943/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 : Supply 12350 (parameters ⟨36,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨36,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨36,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum46W (by norm_num),uniformNum46C (by norm_num),
    fun _ hθ => (geometryCell46 hθ).1,fun _ hθ => (geometryCell46 hθ).2.1⟩

theorem geometryCell47 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨37,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨37,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry47W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (258147439097603679411147/500000000000000000000000) (258752745327378005625503/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry47C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (258147439097603679411147/500000000000000000000000) (258752745327378005625503/500000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 : Supply 12350 (parameters ⟨37,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨37,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨37,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum47W (by norm_num),uniformNum47C (by norm_num),
    fun _ hθ => (geometryCell47 hθ).1,fun _ hθ => (geometryCell47 hθ).2.1⟩

theorem geometryCell48 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨38,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨38,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry48W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (517492641561062834541917/1000000000000000000000000) (518703521710063428152069/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry48C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (517492641561062834541917/1000000000000000000000000) (518703521710063428152069/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 : Supply 12350 (parameters ⟨38,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨38,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨38,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum48W (by norm_num),uniformNum48C (by norm_num),
    fun _ hθ => (geometryCell48 hθ).1,fun _ hθ => (geometryCell48 hθ).2.1⟩

theorem geometryCell49 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12350.grid (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleWide
      (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12350 θ BstLean.Part199.exampleCore
      (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleWide ≤ (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12350 θ BstLean.Part199.exampleCore ≤ (parameters ⟨39,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12350 (sourceIndex ⟨39,by decide⟩) hθ
  norm_num only [scalarRow12350,sourceIndex,BstLean.Part268.cell12350] at hs
  have hw := block0Geometry49W (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (25934520246345915513077/50000000000000000000000) (519901552765370845053131/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  have hk := block0Geometry49C (n := 12350) (by constructor <;> norm_num)
    (θ := θ) (show BstLean.Part255.B (25934520246345915513077/50000000000000000000000) (519901552765370845053131/1000000000000000000000000) θ from
      ⟨(by linarith [hs.1]), (by linarith [hs.2])⟩)
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 : Supply 12350 (parameters ⟨39,by decide⟩)
    (cellLower scalarRow12350.grid (sourceIndex ⟨39,by decide⟩))
    (cellUpper scalarRow12350.grid (sourceIndex ⟨39,by decide⟩)) :=
  ⟨parameters_valid _,uniformNum49W (by norm_num),uniformNum49C (by norm_num),
    fun _ hθ => (geometryCell49 hθ).1,fun _ hθ => (geometryCell49 hθ).2.1⟩


end BstLean.Part269.N12350
