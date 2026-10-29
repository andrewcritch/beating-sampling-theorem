import BstLean.Part264bN12227SClasses
import BstLean.Part264bN12227E10W
import BstLean.Part264bN12227E10C
import BstLean.Part264bN12227O
import BstLean.Part264bN12227WideEBatch0
import BstLean.Part264bN12227WideEBatch1
import BstLean.Part264bN12227WideEBatch2
import BstLean.Part264bN12227WideGeometryBatch0
import BstLean.Part264bN12227WideGeometryBatch1
import BstLean.Part264bN12227WideGeometryBatch2
import BstLean.Part263Covariance
import BstLean.Part263ScalarSupply
namespace BstLean.Part264b.N12227
open Real Set MeasureTheory BstLean.Part130 BstLean.Part182 BstLean.Part255
open BstLean.Part263 (Supply cell cellLower cellUpper scalarRow12227)
theorem num10W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨0,by decide⟩).wlo
      (parameters ⟨0,by decide⟩).whi (parameters ⟨0,by decide⟩).wE
      (parameters ⟨0,by decide⟩).o (parameters ⟨0,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass10W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e10W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num10C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨0,by decide⟩).clo
      (parameters ⟨0,by decide⟩).chi (parameters ⟨0,by decide⟩).cE
      (parameters ⟨0,by decide⟩).o (parameters ⟨0,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass10C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e10C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell10 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨0,by decide⟩).wlo (parameters ⟨0,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨0,by decide⟩).clo (parameters ⟨0,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨0,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨0,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry10W hc
  have hk := geometry10C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply10 : Supply 12227 (parameters ⟨0,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨0,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨0,by decide⟩)) := by
  exact ⟨parameters_valid _,num10W,num10C,
    fun _ hθ => (geometryCell10 hθ).1,
    fun _ hθ => (geometryCell10 hθ).2.1⟩

theorem num11W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨1,by decide⟩).wlo
      (parameters ⟨1,by decide⟩).whi (parameters ⟨1,by decide⟩).wE
      (parameters ⟨1,by decide⟩).o (parameters ⟨1,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass11W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e11W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num11C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨1,by decide⟩).clo
      (parameters ⟨1,by decide⟩).chi (parameters ⟨1,by decide⟩).cE
      (parameters ⟨1,by decide⟩).o (parameters ⟨1,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass11C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e11C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell11 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨1,by decide⟩).wlo (parameters ⟨1,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨1,by decide⟩).clo (parameters ⟨1,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨1,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨1,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry11W hc
  have hk := geometry11C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply11 : Supply 12227 (parameters ⟨1,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨1,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨1,by decide⟩)) := by
  exact ⟨parameters_valid _,num11W,num11C,
    fun _ hθ => (geometryCell11 hθ).1,
    fun _ hθ => (geometryCell11 hθ).2.1⟩

theorem num12W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨2,by decide⟩).wlo
      (parameters ⟨2,by decide⟩).whi (parameters ⟨2,by decide⟩).wE
      (parameters ⟨2,by decide⟩).o (parameters ⟨2,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass12W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e12W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num12C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨2,by decide⟩).clo
      (parameters ⟨2,by decide⟩).chi (parameters ⟨2,by decide⟩).cE
      (parameters ⟨2,by decide⟩).o (parameters ⟨2,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass12C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e12C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell12 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨2,by decide⟩).wlo (parameters ⟨2,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨2,by decide⟩).clo (parameters ⟨2,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨2,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨2,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry12W hc
  have hk := geometry12C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply12 : Supply 12227 (parameters ⟨2,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨2,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨2,by decide⟩)) := by
  exact ⟨parameters_valid _,num12W,num12C,
    fun _ hθ => (geometryCell12 hθ).1,
    fun _ hθ => (geometryCell12 hθ).2.1⟩

theorem num13W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨3,by decide⟩).wlo
      (parameters ⟨3,by decide⟩).whi (parameters ⟨3,by decide⟩).wE
      (parameters ⟨3,by decide⟩).o (parameters ⟨3,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass13W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e13W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num13C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨3,by decide⟩).clo
      (parameters ⟨3,by decide⟩).chi (parameters ⟨3,by decide⟩).cE
      (parameters ⟨3,by decide⟩).o (parameters ⟨3,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass13C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e13C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell13 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨3,by decide⟩).wlo (parameters ⟨3,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨3,by decide⟩).clo (parameters ⟨3,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨3,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨3,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry13W hc
  have hk := geometry13C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply13 : Supply 12227 (parameters ⟨3,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨3,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨3,by decide⟩)) := by
  exact ⟨parameters_valid _,num13W,num13C,
    fun _ hθ => (geometryCell13 hθ).1,
    fun _ hθ => (geometryCell13 hθ).2.1⟩

theorem num14W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨4,by decide⟩).wlo
      (parameters ⟨4,by decide⟩).whi (parameters ⟨4,by decide⟩).wE
      (parameters ⟨4,by decide⟩).o (parameters ⟨4,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass14W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e14W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num14C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨4,by decide⟩).clo
      (parameters ⟨4,by decide⟩).chi (parameters ⟨4,by decide⟩).cE
      (parameters ⟨4,by decide⟩).o (parameters ⟨4,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass14C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e14C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell14 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨4,by decide⟩).wlo (parameters ⟨4,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨4,by decide⟩).clo (parameters ⟨4,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨4,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨4,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry14W hc
  have hk := geometry14C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply14 : Supply 12227 (parameters ⟨4,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨4,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨4,by decide⟩)) := by
  exact ⟨parameters_valid _,num14W,num14C,
    fun _ hθ => (geometryCell14 hθ).1,
    fun _ hθ => (geometryCell14 hθ).2.1⟩

theorem num15W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨5,by decide⟩).wlo
      (parameters ⟨5,by decide⟩).whi (parameters ⟨5,by decide⟩).wE
      (parameters ⟨5,by decide⟩).o (parameters ⟨5,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass15W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e15W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num15C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨5,by decide⟩).clo
      (parameters ⟨5,by decide⟩).chi (parameters ⟨5,by decide⟩).cE
      (parameters ⟨5,by decide⟩).o (parameters ⟨5,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass15C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e15C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell15 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨5,by decide⟩).wlo (parameters ⟨5,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨5,by decide⟩).clo (parameters ⟨5,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨5,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨5,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry15W hc
  have hk := geometry15C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply15 : Supply 12227 (parameters ⟨5,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨5,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨5,by decide⟩)) := by
  exact ⟨parameters_valid _,num15W,num15C,
    fun _ hθ => (geometryCell15 hθ).1,
    fun _ hθ => (geometryCell15 hθ).2.1⟩

theorem num16W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨6,by decide⟩).wlo
      (parameters ⟨6,by decide⟩).whi (parameters ⟨6,by decide⟩).wE
      (parameters ⟨6,by decide⟩).o (parameters ⟨6,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass16W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e16W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num16C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨6,by decide⟩).clo
      (parameters ⟨6,by decide⟩).chi (parameters ⟨6,by decide⟩).cE
      (parameters ⟨6,by decide⟩).o (parameters ⟨6,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass16C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e16C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell16 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨6,by decide⟩).wlo (parameters ⟨6,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨6,by decide⟩).clo (parameters ⟨6,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨6,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨6,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry16W hc
  have hk := geometry16C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply16 : Supply 12227 (parameters ⟨6,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨6,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨6,by decide⟩)) := by
  exact ⟨parameters_valid _,num16W,num16C,
    fun _ hθ => (geometryCell16 hθ).1,
    fun _ hθ => (geometryCell16 hθ).2.1⟩

theorem num17W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨7,by decide⟩).wlo
      (parameters ⟨7,by decide⟩).whi (parameters ⟨7,by decide⟩).wE
      (parameters ⟨7,by decide⟩).o (parameters ⟨7,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass17W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e17W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num17C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨7,by decide⟩).clo
      (parameters ⟨7,by decide⟩).chi (parameters ⟨7,by decide⟩).cE
      (parameters ⟨7,by decide⟩).o (parameters ⟨7,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass17C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e17C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell17 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨7,by decide⟩).wlo (parameters ⟨7,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨7,by decide⟩).clo (parameters ⟨7,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨7,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨7,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry17W hc
  have hk := geometry17C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply17 : Supply 12227 (parameters ⟨7,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨7,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨7,by decide⟩)) := by
  exact ⟨parameters_valid _,num17W,num17C,
    fun _ hθ => (geometryCell17 hθ).1,
    fun _ hθ => (geometryCell17 hθ).2.1⟩

theorem num18W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨8,by decide⟩).wlo
      (parameters ⟨8,by decide⟩).whi (parameters ⟨8,by decide⟩).wE
      (parameters ⟨8,by decide⟩).o (parameters ⟨8,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass18W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e18W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num18C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨8,by decide⟩).clo
      (parameters ⟨8,by decide⟩).chi (parameters ⟨8,by decide⟩).cE
      (parameters ⟨8,by decide⟩).o (parameters ⟨8,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass18C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e18C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell18 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨8,by decide⟩).wlo (parameters ⟨8,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨8,by decide⟩).clo (parameters ⟨8,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨8,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨8,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry18W hc
  have hk := geometry18C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply18 : Supply 12227 (parameters ⟨8,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨8,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨8,by decide⟩)) := by
  exact ⟨parameters_valid _,num18W,num18C,
    fun _ hθ => (geometryCell18 hθ).1,
    fun _ hθ => (geometryCell18 hθ).2.1⟩

theorem num19W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨9,by decide⟩).wlo
      (parameters ⟨9,by decide⟩).whi (parameters ⟨9,by decide⟩).wE
      (parameters ⟨9,by decide⟩).o (parameters ⟨9,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass19W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e19W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num19C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨9,by decide⟩).clo
      (parameters ⟨9,by decide⟩).chi (parameters ⟨9,by decide⟩).cE
      (parameters ⟨9,by decide⟩).o (parameters ⟨9,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass19C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e19C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell19 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨9,by decide⟩).wlo (parameters ⟨9,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨9,by decide⟩).clo (parameters ⟨9,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨9,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨9,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry19W hc
  have hk := geometry19C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply19 : Supply 12227 (parameters ⟨9,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨9,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨9,by decide⟩)) := by
  exact ⟨parameters_valid _,num19W,num19C,
    fun _ hθ => (geometryCell19 hθ).1,
    fun _ hθ => (geometryCell19 hθ).2.1⟩

theorem num20W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨10,by decide⟩).wlo
      (parameters ⟨10,by decide⟩).whi (parameters ⟨10,by decide⟩).wE
      (parameters ⟨10,by decide⟩).o (parameters ⟨10,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass20W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e20W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num20C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨10,by decide⟩).clo
      (parameters ⟨10,by decide⟩).chi (parameters ⟨10,by decide⟩).cE
      (parameters ⟨10,by decide⟩).o (parameters ⟨10,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass20C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e20C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell20 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨10,by decide⟩).wlo (parameters ⟨10,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨10,by decide⟩).clo (parameters ⟨10,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨10,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨10,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry20W hc
  have hk := geometry20C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply20 : Supply 12227 (parameters ⟨10,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨10,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨10,by decide⟩)) := by
  exact ⟨parameters_valid _,num20W,num20C,
    fun _ hθ => (geometryCell20 hθ).1,
    fun _ hθ => (geometryCell20 hθ).2.1⟩

theorem num21W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨11,by decide⟩).wlo
      (parameters ⟨11,by decide⟩).whi (parameters ⟨11,by decide⟩).wE
      (parameters ⟨11,by decide⟩).o (parameters ⟨11,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass21W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e21W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num21C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨11,by decide⟩).clo
      (parameters ⟨11,by decide⟩).chi (parameters ⟨11,by decide⟩).cE
      (parameters ⟨11,by decide⟩).o (parameters ⟨11,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass21C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e21C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell21 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨11,by decide⟩).wlo (parameters ⟨11,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨11,by decide⟩).clo (parameters ⟨11,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨11,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨11,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry21W hc
  have hk := geometry21C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply21 : Supply 12227 (parameters ⟨11,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨11,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨11,by decide⟩)) := by
  exact ⟨parameters_valid _,num21W,num21C,
    fun _ hθ => (geometryCell21 hθ).1,
    fun _ hθ => (geometryCell21 hθ).2.1⟩

theorem num22W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨12,by decide⟩).wlo
      (parameters ⟨12,by decide⟩).whi (parameters ⟨12,by decide⟩).wE
      (parameters ⟨12,by decide⟩).o (parameters ⟨12,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass22W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e22W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num22C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨12,by decide⟩).clo
      (parameters ⟨12,by decide⟩).chi (parameters ⟨12,by decide⟩).cE
      (parameters ⟨12,by decide⟩).o (parameters ⟨12,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass22C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e22C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell22 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨12,by decide⟩).wlo (parameters ⟨12,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨12,by decide⟩).clo (parameters ⟨12,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨12,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨12,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry22W hc
  have hk := geometry22C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply22 : Supply 12227 (parameters ⟨12,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨12,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨12,by decide⟩)) := by
  exact ⟨parameters_valid _,num22W,num22C,
    fun _ hθ => (geometryCell22 hθ).1,
    fun _ hθ => (geometryCell22 hθ).2.1⟩

theorem num23W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨13,by decide⟩).wlo
      (parameters ⟨13,by decide⟩).whi (parameters ⟨13,by decide⟩).wE
      (parameters ⟨13,by decide⟩).o (parameters ⟨13,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass23W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e23W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num23C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨13,by decide⟩).clo
      (parameters ⟨13,by decide⟩).chi (parameters ⟨13,by decide⟩).cE
      (parameters ⟨13,by decide⟩).o (parameters ⟨13,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass23C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e23C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell23 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨13,by decide⟩).wlo (parameters ⟨13,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨13,by decide⟩).clo (parameters ⟨13,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨13,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨13,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry23W hc
  have hk := geometry23C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply23 : Supply 12227 (parameters ⟨13,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨13,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨13,by decide⟩)) := by
  exact ⟨parameters_valid _,num23W,num23C,
    fun _ hθ => (geometryCell23 hθ).1,
    fun _ hθ => (geometryCell23 hθ).2.1⟩

theorem num24W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨14,by decide⟩).wlo
      (parameters ⟨14,by decide⟩).whi (parameters ⟨14,by decide⟩).wE
      (parameters ⟨14,by decide⟩).o (parameters ⟨14,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass24W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e24W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num24C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨14,by decide⟩).clo
      (parameters ⟨14,by decide⟩).chi (parameters ⟨14,by decide⟩).cE
      (parameters ⟨14,by decide⟩).o (parameters ⟨14,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass24C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e24C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell24 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨14,by decide⟩).wlo (parameters ⟨14,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨14,by decide⟩).clo (parameters ⟨14,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨14,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨14,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry24W hc
  have hk := geometry24C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply24 : Supply 12227 (parameters ⟨14,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨14,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨14,by decide⟩)) := by
  exact ⟨parameters_valid _,num24W,num24C,
    fun _ hθ => (geometryCell24 hθ).1,
    fun _ hθ => (geometryCell24 hθ).2.1⟩

theorem num25W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨15,by decide⟩).wlo
      (parameters ⟨15,by decide⟩).whi (parameters ⟨15,by decide⟩).wE
      (parameters ⟨15,by decide⟩).o (parameters ⟨15,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass25W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e25W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num25C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨15,by decide⟩).clo
      (parameters ⟨15,by decide⟩).chi (parameters ⟨15,by decide⟩).cE
      (parameters ⟨15,by decide⟩).o (parameters ⟨15,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass25C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e25C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell25 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨15,by decide⟩).wlo (parameters ⟨15,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨15,by decide⟩).clo (parameters ⟨15,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨15,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨15,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry25W hc
  have hk := geometry25C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply25 : Supply 12227 (parameters ⟨15,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨15,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨15,by decide⟩)) := by
  exact ⟨parameters_valid _,num25W,num25C,
    fun _ hθ => (geometryCell25 hθ).1,
    fun _ hθ => (geometryCell25 hθ).2.1⟩

theorem num26W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨16,by decide⟩).wlo
      (parameters ⟨16,by decide⟩).whi (parameters ⟨16,by decide⟩).wE
      (parameters ⟨16,by decide⟩).o (parameters ⟨16,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass26W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e26W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num26C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨16,by decide⟩).clo
      (parameters ⟨16,by decide⟩).chi (parameters ⟨16,by decide⟩).cE
      (parameters ⟨16,by decide⟩).o (parameters ⟨16,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass26C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e26C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell26 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨16,by decide⟩).wlo (parameters ⟨16,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨16,by decide⟩).clo (parameters ⟨16,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨16,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨16,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry26W hc
  have hk := geometry26C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply26 : Supply 12227 (parameters ⟨16,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨16,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨16,by decide⟩)) := by
  exact ⟨parameters_valid _,num26W,num26C,
    fun _ hθ => (geometryCell26 hθ).1,
    fun _ hθ => (geometryCell26 hθ).2.1⟩

theorem num27W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨17,by decide⟩).wlo
      (parameters ⟨17,by decide⟩).whi (parameters ⟨17,by decide⟩).wE
      (parameters ⟨17,by decide⟩).o (parameters ⟨17,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass27W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e27W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num27C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨17,by decide⟩).clo
      (parameters ⟨17,by decide⟩).chi (parameters ⟨17,by decide⟩).cE
      (parameters ⟨17,by decide⟩).o (parameters ⟨17,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass27C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e27C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell27 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨17,by decide⟩).wlo (parameters ⟨17,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨17,by decide⟩).clo (parameters ⟨17,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨17,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨17,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry27W hc
  have hk := geometry27C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply27 : Supply 12227 (parameters ⟨17,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨17,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨17,by decide⟩)) := by
  exact ⟨parameters_valid _,num27W,num27C,
    fun _ hθ => (geometryCell27 hθ).1,
    fun _ hθ => (geometryCell27 hθ).2.1⟩

theorem num28W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨18,by decide⟩).wlo
      (parameters ⟨18,by decide⟩).whi (parameters ⟨18,by decide⟩).wE
      (parameters ⟨18,by decide⟩).o (parameters ⟨18,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass28W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e28W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num28C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨18,by decide⟩).clo
      (parameters ⟨18,by decide⟩).chi (parameters ⟨18,by decide⟩).cE
      (parameters ⟨18,by decide⟩).o (parameters ⟨18,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass28C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e28C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell28 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨18,by decide⟩).wlo (parameters ⟨18,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨18,by decide⟩).clo (parameters ⟨18,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨18,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨18,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry28W hc
  have hk := geometry28C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply28 : Supply 12227 (parameters ⟨18,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨18,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨18,by decide⟩)) := by
  exact ⟨parameters_valid _,num28W,num28C,
    fun _ hθ => (geometryCell28 hθ).1,
    fun _ hθ => (geometryCell28 hθ).2.1⟩

theorem num29W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨19,by decide⟩).wlo
      (parameters ⟨19,by decide⟩).whi (parameters ⟨19,by decide⟩).wE
      (parameters ⟨19,by decide⟩).o (parameters ⟨19,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass29W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e29W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num29C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨19,by decide⟩).clo
      (parameters ⟨19,by decide⟩).chi (parameters ⟨19,by decide⟩).cE
      (parameters ⟨19,by decide⟩).o (parameters ⟨19,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass29C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e29C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell29 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨19,by decide⟩).wlo (parameters ⟨19,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨19,by decide⟩).clo (parameters ⟨19,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨19,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨19,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry29W hc
  have hk := geometry29C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply29 : Supply 12227 (parameters ⟨19,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨19,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨19,by decide⟩)) := by
  exact ⟨parameters_valid _,num29W,num29C,
    fun _ hθ => (geometryCell29 hθ).1,
    fun _ hθ => (geometryCell29 hθ).2.1⟩

theorem num30W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨20,by decide⟩).wlo
      (parameters ⟨20,by decide⟩).whi (parameters ⟨20,by decide⟩).wE
      (parameters ⟨20,by decide⟩).o (parameters ⟨20,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass30W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e30W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num30C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨20,by decide⟩).clo
      (parameters ⟨20,by decide⟩).chi (parameters ⟨20,by decide⟩).cE
      (parameters ⟨20,by decide⟩).o (parameters ⟨20,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass30C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e30C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell30 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨20,by decide⟩).wlo (parameters ⟨20,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨20,by decide⟩).clo (parameters ⟨20,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨20,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨20,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry30W hc
  have hk := geometry30C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply30 : Supply 12227 (parameters ⟨20,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨20,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨20,by decide⟩)) := by
  exact ⟨parameters_valid _,num30W,num30C,
    fun _ hθ => (geometryCell30 hθ).1,
    fun _ hθ => (geometryCell30 hθ).2.1⟩

theorem num31W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨21,by decide⟩).wlo
      (parameters ⟨21,by decide⟩).whi (parameters ⟨21,by decide⟩).wE
      (parameters ⟨21,by decide⟩).o (parameters ⟨21,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass31W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e31W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num31C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨21,by decide⟩).clo
      (parameters ⟨21,by decide⟩).chi (parameters ⟨21,by decide⟩).cE
      (parameters ⟨21,by decide⟩).o (parameters ⟨21,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass31C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e31C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell31 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨21,by decide⟩).wlo (parameters ⟨21,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨21,by decide⟩).clo (parameters ⟨21,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨21,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨21,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry31W hc
  have hk := geometry31C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply31 : Supply 12227 (parameters ⟨21,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨21,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨21,by decide⟩)) := by
  exact ⟨parameters_valid _,num31W,num31C,
    fun _ hθ => (geometryCell31 hθ).1,
    fun _ hθ => (geometryCell31 hθ).2.1⟩

theorem num32W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨22,by decide⟩).wlo
      (parameters ⟨22,by decide⟩).whi (parameters ⟨22,by decide⟩).wE
      (parameters ⟨22,by decide⟩).o (parameters ⟨22,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass32W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e32W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num32C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨22,by decide⟩).clo
      (parameters ⟨22,by decide⟩).chi (parameters ⟨22,by decide⟩).cE
      (parameters ⟨22,by decide⟩).o (parameters ⟨22,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass32C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e32C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell32 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨22,by decide⟩).wlo (parameters ⟨22,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨22,by decide⟩).clo (parameters ⟨22,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨22,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨22,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry32W hc
  have hk := geometry32C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply32 : Supply 12227 (parameters ⟨22,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨22,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨22,by decide⟩)) := by
  exact ⟨parameters_valid _,num32W,num32C,
    fun _ hθ => (geometryCell32 hθ).1,
    fun _ hθ => (geometryCell32 hθ).2.1⟩

theorem num33W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨23,by decide⟩).wlo
      (parameters ⟨23,by decide⟩).whi (parameters ⟨23,by decide⟩).wE
      (parameters ⟨23,by decide⟩).o (parameters ⟨23,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass33W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e33W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num33C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨23,by decide⟩).clo
      (parameters ⟨23,by decide⟩).chi (parameters ⟨23,by decide⟩).cE
      (parameters ⟨23,by decide⟩).o (parameters ⟨23,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass33C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e33C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell33 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨23,by decide⟩).wlo (parameters ⟨23,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨23,by decide⟩).clo (parameters ⟨23,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨23,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨23,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry33W hc
  have hk := geometry33C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply33 : Supply 12227 (parameters ⟨23,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨23,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨23,by decide⟩)) := by
  exact ⟨parameters_valid _,num33W,num33C,
    fun _ hθ => (geometryCell33 hθ).1,
    fun _ hθ => (geometryCell33 hθ).2.1⟩

theorem num34W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨24,by decide⟩).wlo
      (parameters ⟨24,by decide⟩).whi (parameters ⟨24,by decide⟩).wE
      (parameters ⟨24,by decide⟩).o (parameters ⟨24,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass34W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e34W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num34C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨24,by decide⟩).clo
      (parameters ⟨24,by decide⟩).chi (parameters ⟨24,by decide⟩).cE
      (parameters ⟨24,by decide⟩).o (parameters ⟨24,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass34C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e34C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell34 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨24,by decide⟩).wlo (parameters ⟨24,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨24,by decide⟩).clo (parameters ⟨24,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨24,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨24,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry34W hc
  have hk := geometry34C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply34 : Supply 12227 (parameters ⟨24,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨24,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨24,by decide⟩)) := by
  exact ⟨parameters_valid _,num34W,num34C,
    fun _ hθ => (geometryCell34 hθ).1,
    fun _ hθ => (geometryCell34 hθ).2.1⟩

theorem num35W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨25,by decide⟩).wlo
      (parameters ⟨25,by decide⟩).whi (parameters ⟨25,by decide⟩).wE
      (parameters ⟨25,by decide⟩).o (parameters ⟨25,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass35W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e35W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num35C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨25,by decide⟩).clo
      (parameters ⟨25,by decide⟩).chi (parameters ⟨25,by decide⟩).cE
      (parameters ⟨25,by decide⟩).o (parameters ⟨25,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass35C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e35C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell35 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨25,by decide⟩).wlo (parameters ⟨25,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨25,by decide⟩).clo (parameters ⟨25,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨25,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨25,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry35W hc
  have hk := geometry35C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply35 : Supply 12227 (parameters ⟨25,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨25,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨25,by decide⟩)) := by
  exact ⟨parameters_valid _,num35W,num35C,
    fun _ hθ => (geometryCell35 hθ).1,
    fun _ hθ => (geometryCell35 hθ).2.1⟩

theorem num36W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨26,by decide⟩).wlo
      (parameters ⟨26,by decide⟩).whi (parameters ⟨26,by decide⟩).wE
      (parameters ⟨26,by decide⟩).o (parameters ⟨26,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass36W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e36W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num36C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨26,by decide⟩).clo
      (parameters ⟨26,by decide⟩).chi (parameters ⟨26,by decide⟩).cE
      (parameters ⟨26,by decide⟩).o (parameters ⟨26,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass36C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e36C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell36 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨26,by decide⟩).wlo (parameters ⟨26,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨26,by decide⟩).clo (parameters ⟨26,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨26,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨26,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry36W hc
  have hk := geometry36C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply36 : Supply 12227 (parameters ⟨26,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨26,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨26,by decide⟩)) := by
  exact ⟨parameters_valid _,num36W,num36C,
    fun _ hθ => (geometryCell36 hθ).1,
    fun _ hθ => (geometryCell36 hθ).2.1⟩

theorem num37W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨27,by decide⟩).wlo
      (parameters ⟨27,by decide⟩).whi (parameters ⟨27,by decide⟩).wE
      (parameters ⟨27,by decide⟩).o (parameters ⟨27,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass37W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e37W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num37C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨27,by decide⟩).clo
      (parameters ⟨27,by decide⟩).chi (parameters ⟨27,by decide⟩).cE
      (parameters ⟨27,by decide⟩).o (parameters ⟨27,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass37C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e37C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell37 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨27,by decide⟩).wlo (parameters ⟨27,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨27,by decide⟩).clo (parameters ⟨27,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨27,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨27,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry37W hc
  have hk := geometry37C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply37 : Supply 12227 (parameters ⟨27,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨27,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨27,by decide⟩)) := by
  exact ⟨parameters_valid _,num37W,num37C,
    fun _ hθ => (geometryCell37 hθ).1,
    fun _ hθ => (geometryCell37 hθ).2.1⟩

theorem num38W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨28,by decide⟩).wlo
      (parameters ⟨28,by decide⟩).whi (parameters ⟨28,by decide⟩).wE
      (parameters ⟨28,by decide⟩).o (parameters ⟨28,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass38W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e38W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num38C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨28,by decide⟩).clo
      (parameters ⟨28,by decide⟩).chi (parameters ⟨28,by decide⟩).cE
      (parameters ⟨28,by decide⟩).o (parameters ⟨28,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass38C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e38C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell38 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨28,by decide⟩).wlo (parameters ⟨28,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨28,by decide⟩).clo (parameters ⟨28,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨28,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨28,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry38W hc
  have hk := geometry38C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply38 : Supply 12227 (parameters ⟨28,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨28,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨28,by decide⟩)) := by
  exact ⟨parameters_valid _,num38W,num38C,
    fun _ hθ => (geometryCell38 hθ).1,
    fun _ hθ => (geometryCell38 hθ).2.1⟩

theorem num39W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨29,by decide⟩).wlo
      (parameters ⟨29,by decide⟩).whi (parameters ⟨29,by decide⟩).wE
      (parameters ⟨29,by decide⟩).o (parameters ⟨29,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass39W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e39W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num39C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨29,by decide⟩).clo
      (parameters ⟨29,by decide⟩).chi (parameters ⟨29,by decide⟩).cE
      (parameters ⟨29,by decide⟩).o (parameters ⟨29,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass39C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e39C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell39 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨29,by decide⟩).wlo (parameters ⟨29,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨29,by decide⟩).clo (parameters ⟨29,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨29,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨29,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry39W hc
  have hk := geometry39C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply39 : Supply 12227 (parameters ⟨29,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨29,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨29,by decide⟩)) := by
  exact ⟨parameters_valid _,num39W,num39C,
    fun _ hθ => (geometryCell39 hθ).1,
    fun _ hθ => (geometryCell39 hθ).2.1⟩

theorem num40W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨30,by decide⟩).wlo
      (parameters ⟨30,by decide⟩).whi (parameters ⟨30,by decide⟩).wE
      (parameters ⟨30,by decide⟩).o (parameters ⟨30,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass40W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e40W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num40C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨30,by decide⟩).clo
      (parameters ⟨30,by decide⟩).chi (parameters ⟨30,by decide⟩).cE
      (parameters ⟨30,by decide⟩).o (parameters ⟨30,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass40C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e40C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell40 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨30,by decide⟩).wlo (parameters ⟨30,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨30,by decide⟩).clo (parameters ⟨30,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨30,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨30,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry40W hc
  have hk := geometry40C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply40 : Supply 12227 (parameters ⟨30,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨30,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨30,by decide⟩)) := by
  exact ⟨parameters_valid _,num40W,num40C,
    fun _ hθ => (geometryCell40 hθ).1,
    fun _ hθ => (geometryCell40 hθ).2.1⟩

theorem num41W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨31,by decide⟩).wlo
      (parameters ⟨31,by decide⟩).whi (parameters ⟨31,by decide⟩).wE
      (parameters ⟨31,by decide⟩).o (parameters ⟨31,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass41W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e41W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num41C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨31,by decide⟩).clo
      (parameters ⟨31,by decide⟩).chi (parameters ⟨31,by decide⟩).cE
      (parameters ⟨31,by decide⟩).o (parameters ⟨31,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass41C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e41C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell41 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨31,by decide⟩).wlo (parameters ⟨31,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨31,by decide⟩).clo (parameters ⟨31,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨31,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨31,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry41W hc
  have hk := geometry41C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply41 : Supply 12227 (parameters ⟨31,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨31,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨31,by decide⟩)) := by
  exact ⟨parameters_valid _,num41W,num41C,
    fun _ hθ => (geometryCell41 hθ).1,
    fun _ hθ => (geometryCell41 hθ).2.1⟩

theorem num42W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨32,by decide⟩).wlo
      (parameters ⟨32,by decide⟩).whi (parameters ⟨32,by decide⟩).wE
      (parameters ⟨32,by decide⟩).o (parameters ⟨32,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass42W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e42W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num42C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨32,by decide⟩).clo
      (parameters ⟨32,by decide⟩).chi (parameters ⟨32,by decide⟩).cE
      (parameters ⟨32,by decide⟩).o (parameters ⟨32,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass42C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e42C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell42 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨32,by decide⟩).wlo (parameters ⟨32,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨32,by decide⟩).clo (parameters ⟨32,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨32,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨32,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry42W hc
  have hk := geometry42C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply42 : Supply 12227 (parameters ⟨32,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨32,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨32,by decide⟩)) := by
  exact ⟨parameters_valid _,num42W,num42C,
    fun _ hθ => (geometryCell42 hθ).1,
    fun _ hθ => (geometryCell42 hθ).2.1⟩

theorem num43W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨33,by decide⟩).wlo
      (parameters ⟨33,by decide⟩).whi (parameters ⟨33,by decide⟩).wE
      (parameters ⟨33,by decide⟩).o (parameters ⟨33,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass43W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e43W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num43C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨33,by decide⟩).clo
      (parameters ⟨33,by decide⟩).chi (parameters ⟨33,by decide⟩).cE
      (parameters ⟨33,by decide⟩).o (parameters ⟨33,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass43C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e43C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell43 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨33,by decide⟩).wlo (parameters ⟨33,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨33,by decide⟩).clo (parameters ⟨33,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨33,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨33,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry43W hc
  have hk := geometry43C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply43 : Supply 12227 (parameters ⟨33,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨33,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨33,by decide⟩)) := by
  exact ⟨parameters_valid _,num43W,num43C,
    fun _ hθ => (geometryCell43 hθ).1,
    fun _ hθ => (geometryCell43 hθ).2.1⟩

theorem num44W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨34,by decide⟩).wlo
      (parameters ⟨34,by decide⟩).whi (parameters ⟨34,by decide⟩).wE
      (parameters ⟨34,by decide⟩).o (parameters ⟨34,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass44W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e44W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num44C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨34,by decide⟩).clo
      (parameters ⟨34,by decide⟩).chi (parameters ⟨34,by decide⟩).cE
      (parameters ⟨34,by decide⟩).o (parameters ⟨34,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass44C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e44C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell44 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨34,by decide⟩).wlo (parameters ⟨34,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨34,by decide⟩).clo (parameters ⟨34,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨34,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨34,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry44W hc
  have hk := geometry44C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply44 : Supply 12227 (parameters ⟨34,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨34,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨34,by decide⟩)) := by
  exact ⟨parameters_valid _,num44W,num44C,
    fun _ hθ => (geometryCell44 hθ).1,
    fun _ hθ => (geometryCell44 hθ).2.1⟩

theorem num45W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨35,by decide⟩).wlo
      (parameters ⟨35,by decide⟩).whi (parameters ⟨35,by decide⟩).wE
      (parameters ⟨35,by decide⟩).o (parameters ⟨35,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass45W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e45W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num45C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨35,by decide⟩).clo
      (parameters ⟨35,by decide⟩).chi (parameters ⟨35,by decide⟩).cE
      (parameters ⟨35,by decide⟩).o (parameters ⟨35,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass45C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e45C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell45 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨35,by decide⟩).wlo (parameters ⟨35,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨35,by decide⟩).clo (parameters ⟨35,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨35,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨35,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry45W hc
  have hk := geometry45C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply45 : Supply 12227 (parameters ⟨35,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨35,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨35,by decide⟩)) := by
  exact ⟨parameters_valid _,num45W,num45C,
    fun _ hθ => (geometryCell45 hθ).1,
    fun _ hθ => (geometryCell45 hθ).2.1⟩

theorem num46W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨36,by decide⟩).wlo
      (parameters ⟨36,by decide⟩).whi (parameters ⟨36,by decide⟩).wE
      (parameters ⟨36,by decide⟩).o (parameters ⟨36,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass46W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e46W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num46C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨36,by decide⟩).clo
      (parameters ⟨36,by decide⟩).chi (parameters ⟨36,by decide⟩).cE
      (parameters ⟨36,by decide⟩).o (parameters ⟨36,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass46C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e46C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell46 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨36,by decide⟩).wlo (parameters ⟨36,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨36,by decide⟩).clo (parameters ⟨36,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨36,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨36,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry46W hc
  have hk := geometry46C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply46 : Supply 12227 (parameters ⟨36,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨36,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨36,by decide⟩)) := by
  exact ⟨parameters_valid _,num46W,num46C,
    fun _ hθ => (geometryCell46 hθ).1,
    fun _ hθ => (geometryCell46 hθ).2.1⟩

theorem num47W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨37,by decide⟩).wlo
      (parameters ⟨37,by decide⟩).whi (parameters ⟨37,by decide⟩).wE
      (parameters ⟨37,by decide⟩).o (parameters ⟨37,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass47W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e47W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num47C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨37,by decide⟩).clo
      (parameters ⟨37,by decide⟩).chi (parameters ⟨37,by decide⟩).cE
      (parameters ⟨37,by decide⟩).o (parameters ⟨37,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass47C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e47C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell47 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨37,by decide⟩).wlo (parameters ⟨37,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨37,by decide⟩).clo (parameters ⟨37,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨37,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨37,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry47W hc
  have hk := geometry47C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply47 : Supply 12227 (parameters ⟨37,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨37,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨37,by decide⟩)) := by
  exact ⟨parameters_valid _,num47W,num47C,
    fun _ hθ => (geometryCell47 hθ).1,
    fun _ hθ => (geometryCell47 hθ).2.1⟩

theorem num48W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨38,by decide⟩).wlo
      (parameters ⟨38,by decide⟩).whi (parameters ⟨38,by decide⟩).wE
      (parameters ⟨38,by decide⟩).o (parameters ⟨38,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass48W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e48W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num48C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨38,by decide⟩).clo
      (parameters ⟨38,by decide⟩).chi (parameters ⟨38,by decide⟩).cE
      (parameters ⟨38,by decide⟩).o (parameters ⟨38,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass48C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e48C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell48 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨38,by decide⟩).wlo (parameters ⟨38,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨38,by decide⟩).clo (parameters ⟨38,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨38,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨38,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry48W hc
  have hk := geometry48C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply48 : Supply 12227 (parameters ⟨38,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨38,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨38,by decide⟩)) := by
  exact ⟨parameters_valid _,num48W,num48C,
    fun _ hθ => (geometryCell48 hθ).1,
    fun _ hθ => (geometryCell48 hθ).2.1⟩

theorem num49W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨39,by decide⟩).wlo
      (parameters ⟨39,by decide⟩).whi (parameters ⟨39,by decide⟩).wE
      (parameters ⟨39,by decide⟩).o (parameters ⟨39,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass49W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e49W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num49C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨39,by decide⟩).clo
      (parameters ⟨39,by decide⟩).chi (parameters ⟨39,by decide⟩).cE
      (parameters ⟨39,by decide⟩).o (parameters ⟨39,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass49C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e49C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell49 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨39,by decide⟩).wlo (parameters ⟨39,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨39,by decide⟩).clo (parameters ⟨39,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨39,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨39,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry49W hc
  have hk := geometry49C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply49 : Supply 12227 (parameters ⟨39,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨39,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨39,by decide⟩)) := by
  exact ⟨parameters_valid _,num49W,num49C,
    fun _ hθ => (geometryCell49 hθ).1,
    fun _ hθ => (geometryCell49 hθ).2.1⟩

theorem num50W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨40,by decide⟩).wlo
      (parameters ⟨40,by decide⟩).whi (parameters ⟨40,by decide⟩).wE
      (parameters ⟨40,by decide⟩).o (parameters ⟨40,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass50W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e50W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num50C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨40,by decide⟩).clo
      (parameters ⟨40,by decide⟩).chi (parameters ⟨40,by decide⟩).cE
      (parameters ⟨40,by decide⟩).o (parameters ⟨40,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass50C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e50C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell50 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨40,by decide⟩).wlo (parameters ⟨40,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨40,by decide⟩).clo (parameters ⟨40,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨40,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨40,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry50W hc
  have hk := geometry50C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply50 : Supply 12227 (parameters ⟨40,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨40,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨40,by decide⟩)) := by
  exact ⟨parameters_valid _,num50W,num50C,
    fun _ hθ => (geometryCell50 hθ).1,
    fun _ hθ => (geometryCell50 hθ).2.1⟩

theorem num51W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨41,by decide⟩).wlo
      (parameters ⟨41,by decide⟩).whi (parameters ⟨41,by decide⟩).wE
      (parameters ⟨41,by decide⟩).o (parameters ⟨41,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass51W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e51W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num51C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨41,by decide⟩).clo
      (parameters ⟨41,by decide⟩).chi (parameters ⟨41,by decide⟩).cE
      (parameters ⟨41,by decide⟩).o (parameters ⟨41,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass51C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e51C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell51 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨41,by decide⟩).wlo (parameters ⟨41,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨41,by decide⟩).clo (parameters ⟨41,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨41,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨41,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry51W hc
  have hk := geometry51C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply51 : Supply 12227 (parameters ⟨41,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨41,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨41,by decide⟩)) := by
  exact ⟨parameters_valid _,num51W,num51C,
    fun _ hθ => (geometryCell51 hθ).1,
    fun _ hθ => (geometryCell51 hθ).2.1⟩

theorem num52W :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨42,by decide⟩).wlo
      (parameters ⟨42,by decide⟩).whi (parameters ⟨42,by decide⟩).wE
      (parameters ⟨42,by decide⟩).o (parameters ⟨42,by decide⟩).wS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass52W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e52W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num52C :
    BstLean.Part246.ta_num_sharp 12227 (parameters ⟨42,by decide⟩).clo
      (parameters ⟨42,by decide⟩).chi (parameters ⟨42,by decide⟩).cE
      (parameters ⟨42,by decide⟩).o (parameters ⟨42,by decide⟩).cS
      (BstLean.Part263.maskSlack 12227) 46 := by
  change BstLean.Part246.ta_num_sharp 12227 _ _ _ _ _ maskSlack 46
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass52C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e52C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem geometryCell52 {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleWide
      (parameters ⟨42,by decide⟩).wlo (parameters ⟨42,by decide⟩).whi ∧
    BstLean.Part199.OverlapGuard 12227 θ BstLean.Part199.exampleCore
      (parameters ⟨42,by decide⟩).clo (parameters ⟨42,by decide⟩).chi ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨42,by decide⟩).cRadius := by
  have hs := BstLean.Part263.scalarRow_cell_subset scalarRow12227
    (sourceIndex ⟨42,by decide⟩) hθ
  have hc := hs
  norm_num only [scalarRow12227, sourceIndex, BstLean.Part263.cell12227] at hc
  have hw := geometry52W hc
  have hk := geometry52C hc
  exact ⟨hw.1,hk.1,hw.2,hk.2⟩

theorem supply52 : Supply 12227 (parameters ⟨42,by decide⟩)
    (cellLower scalarRow12227.grid (sourceIndex ⟨42,by decide⟩))
    (cellUpper scalarRow12227.grid (sourceIndex ⟨42,by decide⟩)) := by
  exact ⟨parameters_valid _,num52W,num52C,
    fun _ hθ => (geometryCell52 hθ).1,
    fun _ hθ => (geometryCell52 hθ).2.1⟩

theorem supplies12227 (j : Fin 43) : Supply 12227 (parameters j)
    (cellLower scalarRow12227.grid (sourceIndex j))
    (cellUpper scalarRow12227.grid (sourceIndex j)) := by
  match j with
  | ⟨0,_⟩ => exact supply10
  | ⟨1,_⟩ => exact supply11
  | ⟨2,_⟩ => exact supply12
  | ⟨3,_⟩ => exact supply13
  | ⟨4,_⟩ => exact supply14
  | ⟨5,_⟩ => exact supply15
  | ⟨6,_⟩ => exact supply16
  | ⟨7,_⟩ => exact supply17
  | ⟨8,_⟩ => exact supply18
  | ⟨9,_⟩ => exact supply19
  | ⟨10,_⟩ => exact supply20
  | ⟨11,_⟩ => exact supply21
  | ⟨12,_⟩ => exact supply22
  | ⟨13,_⟩ => exact supply23
  | ⟨14,_⟩ => exact supply24
  | ⟨15,_⟩ => exact supply25
  | ⟨16,_⟩ => exact supply26
  | ⟨17,_⟩ => exact supply27
  | ⟨18,_⟩ => exact supply28
  | ⟨19,_⟩ => exact supply29
  | ⟨20,_⟩ => exact supply30
  | ⟨21,_⟩ => exact supply31
  | ⟨22,_⟩ => exact supply32
  | ⟨23,_⟩ => exact supply33
  | ⟨24,_⟩ => exact supply34
  | ⟨25,_⟩ => exact supply35
  | ⟨26,_⟩ => exact supply36
  | ⟨27,_⟩ => exact supply37
  | ⟨28,_⟩ => exact supply38
  | ⟨29,_⟩ => exact supply39
  | ⟨30,_⟩ => exact supply40
  | ⟨31,_⟩ => exact supply41
  | ⟨32,_⟩ => exact supply42
  | ⟨33,_⟩ => exact supply43
  | ⟨34,_⟩ => exact supply44
  | ⟨35,_⟩ => exact supply45
  | ⟨36,_⟩ => exact supply46
  | ⟨37,_⟩ => exact supply47
  | ⟨38,_⟩ => exact supply48
  | ⟨39,_⟩ => exact supply49
  | ⟨40,_⟩ => exact supply50
  | ⟨41,_⟩ => exact supply51
  | ⟨42,_⟩ => exact supply52
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem radii12227 (j : Fin 43) {θ : ℝ}
    (hθ : θ ∈ cell scalarRow12227.grid (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12227 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius := by
  match j with
  | ⟨0,_⟩ => exact (geometryCell10 hθ).2.2
  | ⟨1,_⟩ => exact (geometryCell11 hθ).2.2
  | ⟨2,_⟩ => exact (geometryCell12 hθ).2.2
  | ⟨3,_⟩ => exact (geometryCell13 hθ).2.2
  | ⟨4,_⟩ => exact (geometryCell14 hθ).2.2
  | ⟨5,_⟩ => exact (geometryCell15 hθ).2.2
  | ⟨6,_⟩ => exact (geometryCell16 hθ).2.2
  | ⟨7,_⟩ => exact (geometryCell17 hθ).2.2
  | ⟨8,_⟩ => exact (geometryCell18 hθ).2.2
  | ⟨9,_⟩ => exact (geometryCell19 hθ).2.2
  | ⟨10,_⟩ => exact (geometryCell20 hθ).2.2
  | ⟨11,_⟩ => exact (geometryCell21 hθ).2.2
  | ⟨12,_⟩ => exact (geometryCell22 hθ).2.2
  | ⟨13,_⟩ => exact (geometryCell23 hθ).2.2
  | ⟨14,_⟩ => exact (geometryCell24 hθ).2.2
  | ⟨15,_⟩ => exact (geometryCell25 hθ).2.2
  | ⟨16,_⟩ => exact (geometryCell26 hθ).2.2
  | ⟨17,_⟩ => exact (geometryCell27 hθ).2.2
  | ⟨18,_⟩ => exact (geometryCell28 hθ).2.2
  | ⟨19,_⟩ => exact (geometryCell29 hθ).2.2
  | ⟨20,_⟩ => exact (geometryCell30 hθ).2.2
  | ⟨21,_⟩ => exact (geometryCell31 hθ).2.2
  | ⟨22,_⟩ => exact (geometryCell32 hθ).2.2
  | ⟨23,_⟩ => exact (geometryCell33 hθ).2.2
  | ⟨24,_⟩ => exact (geometryCell34 hθ).2.2
  | ⟨25,_⟩ => exact (geometryCell35 hθ).2.2
  | ⟨26,_⟩ => exact (geometryCell36 hθ).2.2
  | ⟨27,_⟩ => exact (geometryCell37 hθ).2.2
  | ⟨28,_⟩ => exact (geometryCell38 hθ).2.2
  | ⟨29,_⟩ => exact (geometryCell39 hθ).2.2
  | ⟨30,_⟩ => exact (geometryCell40 hθ).2.2
  | ⟨31,_⟩ => exact (geometryCell41 hθ).2.2
  | ⟨32,_⟩ => exact (geometryCell42 hθ).2.2
  | ⟨33,_⟩ => exact (geometryCell43 hθ).2.2
  | ⟨34,_⟩ => exact (geometryCell44 hθ).2.2
  | ⟨35,_⟩ => exact (geometryCell45 hθ).2.2
  | ⟨36,_⟩ => exact (geometryCell46 hθ).2.2
  | ⟨37,_⟩ => exact (geometryCell47 hθ).2.2
  | ⟨38,_⟩ => exact (geometryCell48 hθ).2.2
  | ⟨39,_⟩ => exact (geometryCell49 hθ).2.2
  | ⟨40,_⟩ => exact (geometryCell50 hθ).2.2
  | ⟨41,_⟩ => exact (geometryCell51 hθ).2.2
  | ⟨42,_⟩ => exact (geometryCell52 hθ).2.2
  | ⟨j+43,h⟩ => exact False.elim (by omega)

end BstLean.Part264b.N12227
