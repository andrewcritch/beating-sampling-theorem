import BstLean.Part255SClasses
import BstLean.Part255O
import BstLean.Part255Geometry49
import BstLean.Part255Geometry50
import BstLean.Part255Geometry51
import BstLean.Part255Geometry52

namespace BstLean.Part255
open Real Set BstLean.Part182
open BstLean.Part251 (noiseNode proposedThetaUpper)
open BstLean.Part254 (cell cellLower cellUpper)
theorem num10W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨0,by decide⟩).wlo
      (parameters ⟨0,by decide⟩).whi (parameters ⟨0,by decide⟩).wE
      (parameters ⟨0,by decide⟩).o (parameters ⟨0,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass10W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e10W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num10C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨0,by decide⟩).clo
      (parameters ⟨0,by decide⟩).chi (parameters ⟨0,by decide⟩).cE
      (parameters ⟨0,by decide⟩).o (parameters ⟨0,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass10C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e10C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell10 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨0,by decide⟩)) :
    B (2831966295480402052191389 / 6000000000000000000000000) (28391629250284422574105279 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 10 ≤ θ at hl
  change θ ≤ noiseNode 11 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply10 : Supply (parameters ⟨0,by decide⟩)
    (cellLower (sourceIndex ⟨0,by decide⟩)) (cellUpper (sourceIndex ⟨0,by decide⟩)) := by
  refine ⟨valid0,num10W,num10C,?_,?_⟩
  · intro θ hθ
    exact (geometry10W (fullCell10 hθ)).1
  · intro θ hθ
    exact (geometry10C (fullCell10 hθ)).1

theorem radius10 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨0,by decide⟩).cRadius :=
  ⟨(geometry10W (fullCell10 hθ)).2,(geometry10C (fullCell10 hθ)).2⟩

theorem num11W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨1,by decide⟩).wlo
      (parameters ⟨1,by decide⟩).whi (parameters ⟨1,by decide⟩).wE
      (parameters ⟨1,by decide⟩).o (parameters ⟨1,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass11W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e11W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num11C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨1,by decide⟩).clo
      (parameters ⟨1,by decide⟩).chi (parameters ⟨1,by decide⟩).cE
      (parameters ⟨1,by decide⟩).o (parameters ⟨1,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass11C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e11C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell11 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨1,by decide⟩)) :
    B (28391629250284422574105279 / 60000000000000000000000000) (2371966295480402052191389 / 5000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 11 ≤ θ at hl
  change θ ≤ noiseNode 12 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply11 : Supply (parameters ⟨1,by decide⟩)
    (cellLower (sourceIndex ⟨1,by decide⟩)) (cellUpper (sourceIndex ⟨1,by decide⟩)) := by
  refine ⟨valid1,num11W,num11C,?_,?_⟩
  · intro θ hθ
    exact (geometry11W (fullCell11 hθ)).1
  · intro θ hθ
    exact (geometry11C (fullCell11 hθ)).1

theorem radius11 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨1,by decide⟩).cRadius :=
  ⟨(geometry11W (fullCell11 hθ)).2,(geometry11C (fullCell11 hθ)).2⟩

theorem num12W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨2,by decide⟩).wlo
      (parameters ⟨2,by decide⟩).whi (parameters ⟨2,by decide⟩).wE
      (parameters ⟨2,by decide⟩).o (parameters ⟨2,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass12W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e12W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num12C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨2,by decide⟩).clo
      (parameters ⟨2,by decide⟩).chi (parameters ⟨2,by decide⟩).cE
      (parameters ⟨2,by decide⟩).o (parameters ⟨2,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass12C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e12C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell12 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨2,by decide⟩)) :
    B (2371966295480402052191389 / 5000000000000000000000000) (28535561841245226678488057 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 12 ≤ θ at hl
  change θ ≤ noiseNode 13 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply12 : Supply (parameters ⟨2,by decide⟩)
    (cellLower (sourceIndex ⟨2,by decide⟩)) (cellUpper (sourceIndex ⟨2,by decide⟩)) := by
  refine ⟨valid2,num12W,num12C,?_,?_⟩
  · intro θ hθ
    exact (geometry12W (fullCell12 hθ)).1
  · intro θ hθ
    exact (geometry12C (fullCell12 hθ)).1

theorem radius12 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨2,by decide⟩).cRadius :=
  ⟨(geometry12W (fullCell12 hθ)).2,(geometry12C (fullCell12 hθ)).2⟩

theorem num13W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨3,by decide⟩).wlo
      (parameters ⟨3,by decide⟩).whi (parameters ⟨3,by decide⟩).wE
      (parameters ⟨3,by decide⟩).o (parameters ⟨3,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass13W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e13W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num13C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨3,by decide⟩).clo
      (parameters ⟨3,by decide⟩).chi (parameters ⟨3,by decide⟩).cE
      (parameters ⟨3,by decide⟩).o (parameters ⟨3,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass13C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e13C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell13 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨3,by decide⟩)) :
    B (28535561841245226678488057 / 60000000000000000000000000) (14303764068362814365339723 / 30000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 13 ≤ θ at hl
  change θ ≤ noiseNode 14 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply13 : Supply (parameters ⟨3,by decide⟩)
    (cellLower (sourceIndex ⟨3,by decide⟩)) (cellUpper (sourceIndex ⟨3,by decide⟩)) := by
  refine ⟨valid3,num13W,num13C,?_,?_⟩
  · intro θ hθ
    exact (geometry13W (fullCell13 hθ)).1
  · intro θ hθ
    exact (geometry13C (fullCell13 hθ)).1

theorem radius13 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨3,by decide⟩).cRadius :=
  ⟨(geometry13W (fullCell13 hθ)).2,(geometry13C (fullCell13 hθ)).2⟩

theorem num14W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨4,by decide⟩).wlo
      (parameters ⟨4,by decide⟩).whi (parameters ⟨4,by decide⟩).wE
      (parameters ⟨4,by decide⟩).o (parameters ⟨4,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass14W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e14W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num14C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨4,by decide⟩).clo
      (parameters ⟨4,by decide⟩).chi (parameters ⟨4,by decide⟩).cE
      (parameters ⟨4,by decide⟩).o (parameters ⟨4,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass14C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e14C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell14 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨4,by decide⟩)) :
    B (14303764068362814365339723 / 30000000000000000000000000) (1911966295480402052191389 / 4000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 14 ≤ θ at hl
  change θ ≤ noiseNode 15 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply14 : Supply (parameters ⟨4,by decide⟩)
    (cellLower (sourceIndex ⟨4,by decide⟩)) (cellUpper (sourceIndex ⟨4,by decide⟩)) := by
  refine ⟨valid4,num14W,num14C,?_,?_⟩
  · intro θ hθ
    exact (geometry14W (fullCell14 hθ)).1
  · intro θ hθ
    exact (geometry14C (fullCell14 hθ)).1

theorem radius14 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨4,by decide⟩).cRadius :=
  ⟨(geometry14W (fullCell14 hθ)).2,(geometry14C (fullCell14 hθ)).2⟩

theorem num15W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨5,by decide⟩).wlo
      (parameters ⟨5,by decide⟩).whi (parameters ⟨5,by decide⟩).wE
      (parameters ⟨5,by decide⟩).o (parameters ⟨5,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass15W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e15W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num15C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨5,by decide⟩).clo
      (parameters ⟨5,by decide⟩).chi (parameters ⟨5,by decide⟩).cE
      (parameters ⟨5,by decide⟩).o (parameters ⟨5,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass15C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e15C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell15 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨5,by decide⟩)) :
    B (1911966295480402052191389 / 4000000000000000000000000) (1796966295480402052191389 / 3750000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 15 ≤ θ at hl
  change θ ≤ noiseNode 16 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply15 : Supply (parameters ⟨5,by decide⟩)
    (cellLower (sourceIndex ⟨5,by decide⟩)) (cellUpper (sourceIndex ⟨5,by decide⟩)) := by
  refine ⟨valid5,num15W,num15C,?_,?_⟩
  · intro θ hθ
    exact (geometry15W (fullCell15 hθ)).1
  · intro θ hθ
    exact (geometry15C (fullCell15 hθ)).1

theorem radius15 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨5,by decide⟩).cRadius :=
  ⟨(geometry15W (fullCell15 hθ)).2,(geometry15C (fullCell15 hθ)).2⟩

theorem num16W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨6,by decide⟩).wlo
      (parameters ⟨6,by decide⟩).whi (parameters ⟨6,by decide⟩).wE
      (parameters ⟨6,by decide⟩).o (parameters ⟨6,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass16W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e16W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num16C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨6,by decide⟩).clo
      (parameters ⟨6,by decide⟩).chi (parameters ⟨6,by decide⟩).cE
      (parameters ⟨6,by decide⟩).o (parameters ⟨6,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass16C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e16C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell16 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨6,by decide⟩)) :
    B (1796966295480402052191389 / 3750000000000000000000000) (28823427023166834887253613 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 16 ≤ θ at hl
  change θ ≤ noiseNode 17 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply16 : Supply (parameters ⟨6,by decide⟩)
    (cellLower (sourceIndex ⟨6,by decide⟩)) (cellUpper (sourceIndex ⟨6,by decide⟩)) := by
  refine ⟨valid6,num16W,num16C,?_,?_⟩
  · intro θ hθ
    exact (geometry16W (fullCell16 hθ)).1
  · intro θ hθ
    exact (geometry16C (fullCell16 hθ)).1

theorem radius16 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨6,by decide⟩).cRadius :=
  ⟨(geometry16W (fullCell16 hθ)).2,(geometry16C (fullCell16 hθ)).2⟩

theorem num17W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨7,by decide⟩).wlo
      (parameters ⟨7,by decide⟩).whi (parameters ⟨7,by decide⟩).wE
      (parameters ⟨7,by decide⟩).o (parameters ⟨7,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass17W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e17W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num17C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨7,by decide⟩).clo
      (parameters ⟨7,by decide⟩).chi (parameters ⟨7,by decide⟩).cE
      (parameters ⟨7,by decide⟩).o (parameters ⟨7,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass17C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e17C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell17 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨7,by decide⟩)) :
    B (28823427023166834887253613 / 60000000000000000000000000) (4815898886441206156574167 / 10000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 17 ≤ θ at hl
  change θ ≤ noiseNode 18 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply17 : Supply (parameters ⟨7,by decide⟩)
    (cellLower (sourceIndex ⟨7,by decide⟩)) (cellUpper (sourceIndex ⟨7,by decide⟩)) := by
  refine ⟨valid7,num17W,num17C,?_,?_⟩
  · intro θ hθ
    exact (geometry17W (fullCell17 hθ)).1
  · intro θ hθ
    exact (geometry17C (fullCell17 hθ)).1

theorem radius17 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨7,by decide⟩).cRadius :=
  ⟨(geometry17W (fullCell17 hθ)).2,(geometry17C (fullCell17 hθ)).2⟩

theorem num18W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨8,by decide⟩).wlo
      (parameters ⟨8,by decide⟩).whi (parameters ⟨8,by decide⟩).wE
      (parameters ⟨8,by decide⟩).o (parameters ⟨8,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass18W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e18W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num18C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨8,by decide⟩).clo
      (parameters ⟨8,by decide⟩).chi (parameters ⟨8,by decide⟩).cE
      (parameters ⟨8,by decide⟩).o (parameters ⟨8,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass18C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e18C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell18 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨8,by decide⟩)) :
    B (4815898886441206156574167 / 10000000000000000000000000) (28967359614127638991636391 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 18 ≤ θ at hl
  change θ ≤ noiseNode 19 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply18 : Supply (parameters ⟨8,by decide⟩)
    (cellLower (sourceIndex ⟨8,by decide⟩)) (cellUpper (sourceIndex ⟨8,by decide⟩)) := by
  refine ⟨valid8,num18W,num18C,?_,?_⟩
  · intro θ hθ
    exact (geometry18W (fullCell18 hθ)).1
  · intro θ hθ
    exact (geometry18C (fullCell18 hθ)).1

theorem radius18 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨8,by decide⟩).cRadius :=
  ⟨(geometry18W (fullCell18 hθ)).2,(geometry18C (fullCell18 hθ)).2⟩

theorem num19W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨9,by decide⟩).wlo
      (parameters ⟨9,by decide⟩).whi (parameters ⟨9,by decide⟩).wE
      (parameters ⟨9,by decide⟩).o (parameters ⟨9,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass19W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e19W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num19C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨9,by decide⟩).clo
      (parameters ⟨9,by decide⟩).chi (parameters ⟨9,by decide⟩).cE
      (parameters ⟨9,by decide⟩).o (parameters ⟨9,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass19C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e19C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell19 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨9,by decide⟩)) :
    B (28967359614127638991636391 / 60000000000000000000000000) (1451966295480402052191389 / 3000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 19 ≤ θ at hl
  change θ ≤ noiseNode 20 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply19 : Supply (parameters ⟨9,by decide⟩)
    (cellLower (sourceIndex ⟨9,by decide⟩)) (cellUpper (sourceIndex ⟨9,by decide⟩)) := by
  refine ⟨valid9,num19W,num19C,?_,?_⟩
  · intro θ hθ
    exact (geometry19W (fullCell19 hθ)).1
  · intro θ hθ
    exact (geometry19C (fullCell19 hθ)).1

theorem radius19 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨9,by decide⟩).cRadius :=
  ⟨(geometry19W (fullCell19 hθ)).2,(geometry19C (fullCell19 hθ)).2⟩

theorem num20W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨10,by decide⟩).wlo
      (parameters ⟨10,by decide⟩).whi (parameters ⟨10,by decide⟩).wE
      (parameters ⟨10,by decide⟩).o (parameters ⟨10,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass20W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e20W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num20C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨10,by decide⟩).clo
      (parameters ⟨10,by decide⟩).chi (parameters ⟨10,by decide⟩).cE
      (parameters ⟨10,by decide⟩).o (parameters ⟨10,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass20C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e20C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell20 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨10,by decide⟩)) :
    B (1451966295480402052191389 / 3000000000000000000000000) (9703764068362814365339723 / 20000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 20 ≤ θ at hl
  change θ ≤ noiseNode 21 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply20 : Supply (parameters ⟨10,by decide⟩)
    (cellLower (sourceIndex ⟨10,by decide⟩)) (cellUpper (sourceIndex ⟨10,by decide⟩)) := by
  refine ⟨valid10,num20W,num20C,?_,?_⟩
  · intro θ hθ
    exact (geometry20W (fullCell20 hθ)).1
  · intro θ hθ
    exact (geometry20C (fullCell20 hθ)).1

theorem radius20 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨10,by decide⟩).cRadius :=
  ⟨(geometry20W (fullCell20 hθ)).2,(geometry20C (fullCell20 hθ)).2⟩

theorem num21W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨11,by decide⟩).wlo
      (parameters ⟨11,by decide⟩).whi (parameters ⟨11,by decide⟩).wE
      (parameters ⟨11,by decide⟩).o (parameters ⟨11,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass21W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e21W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num21C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨11,by decide⟩).clo
      (parameters ⟨11,by decide⟩).chi (parameters ⟨11,by decide⟩).cE
      (parameters ⟨11,by decide⟩).o (parameters ⟨11,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass21C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e21C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell21 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨11,by decide⟩)) :
    B (9703764068362814365339723 / 20000000000000000000000000) (14591629250284422574105279 / 30000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 21 ≤ θ at hl
  change θ ≤ noiseNode 22 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply21 : Supply (parameters ⟨11,by decide⟩)
    (cellLower (sourceIndex ⟨11,by decide⟩)) (cellUpper (sourceIndex ⟨11,by decide⟩)) := by
  refine ⟨valid11,num21W,num21C,?_,?_⟩
  · intro θ hθ
    exact (geometry21W (fullCell21 hθ)).1
  · intro θ hθ
    exact (geometry21C (fullCell21 hθ)).1

theorem radius21 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨11,by decide⟩).cRadius :=
  ⟨(geometry21W (fullCell21 hθ)).2,(geometry21C (fullCell21 hθ)).2⟩

theorem num22W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨12,by decide⟩).wlo
      (parameters ⟨12,by decide⟩).whi (parameters ⟨12,by decide⟩).wE
      (parameters ⟨12,by decide⟩).o (parameters ⟨12,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass22W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e22W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num22C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨12,by decide⟩).clo
      (parameters ⟨12,by decide⟩).chi (parameters ⟨12,by decide⟩).cE
      (parameters ⟨12,by decide⟩).o (parameters ⟨12,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass22C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e22C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell22 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨12,by decide⟩)) :
    B (14591629250284422574105279 / 30000000000000000000000000) (29255224796049247200401947 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 22 ≤ θ at hl
  change θ ≤ noiseNode 23 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply22 : Supply (parameters ⟨12,by decide⟩)
    (cellLower (sourceIndex ⟨12,by decide⟩)) (cellUpper (sourceIndex ⟨12,by decide⟩)) := by
  refine ⟨valid12,num22W,num22C,?_,?_⟩
  · intro θ hθ
    exact (geometry22W (fullCell22 hθ)).1
  · intro θ hθ
    exact (geometry22C (fullCell22 hθ)).1

theorem radius22 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨12,by decide⟩).cRadius :=
  ⟨(geometry22W (fullCell22 hθ)).2,(geometry22C (fullCell22 hθ)).2⟩

theorem num23W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨13,by decide⟩).wlo
      (parameters ⟨13,by decide⟩).whi (parameters ⟨13,by decide⟩).wE
      (parameters ⟨13,by decide⟩).o (parameters ⟨13,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass23W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e23W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num23C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨13,by decide⟩).clo
      (parameters ⟨13,by decide⟩).chi (parameters ⟨13,by decide⟩).cE
      (parameters ⟨13,by decide⟩).o (parameters ⟨13,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass23C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e23C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell23 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨13,by decide⟩)) :
    B (29255224796049247200401947 / 60000000000000000000000000) (1221966295480402052191389 / 2500000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 23 ≤ θ at hl
  change θ ≤ noiseNode 24 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply23 : Supply (parameters ⟨13,by decide⟩)
    (cellLower (sourceIndex ⟨13,by decide⟩)) (cellUpper (sourceIndex ⟨13,by decide⟩)) := by
  refine ⟨valid13,num23W,num23C,?_,?_⟩
  · intro θ hθ
    exact (geometry23W (fullCell23 hθ)).1
  · intro θ hθ
    exact (geometry23C (fullCell23 hθ)).1

theorem radius23 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨13,by decide⟩).cRadius :=
  ⟨(geometry23W (fullCell23 hθ)).2,(geometry23C (fullCell23 hθ)).2⟩

theorem num24W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨14,by decide⟩).wlo
      (parameters ⟨14,by decide⟩).whi (parameters ⟨14,by decide⟩).wE
      (parameters ⟨14,by decide⟩).o (parameters ⟨14,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass24W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e24W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num24C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨14,by decide⟩).clo
      (parameters ⟨14,by decide⟩).chi (parameters ⟨14,by decide⟩).cE
      (parameters ⟨14,by decide⟩).o (parameters ⟨14,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass24C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e24C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell24 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨14,by decide⟩)) :
    B (1221966295480402052191389 / 2500000000000000000000000) (1175966295480402052191389 / 2400000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 24 ≤ θ at hl
  change θ ≤ noiseNode 25 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply24 : Supply (parameters ⟨14,by decide⟩)
    (cellLower (sourceIndex ⟨14,by decide⟩)) (cellUpper (sourceIndex ⟨14,by decide⟩)) := by
  refine ⟨valid14,num24W,num24C,?_,?_⟩
  · intro θ hθ
    exact (geometry24W (fullCell24 hθ)).1
  · intro θ hθ
    exact (geometry24C (fullCell24 hθ)).1

theorem radius24 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨14,by decide⟩).cRadius :=
  ⟨(geometry24W (fullCell24 hθ)).2,(geometry24C (fullCell24 hθ)).2⟩

theorem num25W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨15,by decide⟩).wlo
      (parameters ⟨15,by decide⟩).whi (parameters ⟨15,by decide⟩).wE
      (parameters ⟨15,by decide⟩).o (parameters ⟨15,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass25W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e25W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num25C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨15,by decide⟩).clo
      (parameters ⟨15,by decide⟩).chi (parameters ⟨15,by decide⟩).cE
      (parameters ⟨15,by decide⟩).o (parameters ⟨15,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass25C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e25C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell25 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨15,by decide⟩)) :
    B (1175966295480402052191389 / 2400000000000000000000000) (14735561841245226678488057 / 30000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 25 ≤ θ at hl
  change θ ≤ noiseNode 26 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply25 : Supply (parameters ⟨15,by decide⟩)
    (cellLower (sourceIndex ⟨15,by decide⟩)) (cellUpper (sourceIndex ⟨15,by decide⟩)) := by
  refine ⟨valid15,num25W,num25C,?_,?_⟩
  · intro θ hθ
    exact (geometry25W (fullCell25 hθ)).1
  · intro θ hθ
    exact (geometry25C (fullCell25 hθ)).1

theorem radius25 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨15,by decide⟩).cRadius :=
  ⟨(geometry25W (fullCell25 hθ)).2,(geometry25C (fullCell25 hθ)).2⟩

theorem num26W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨16,by decide⟩).wlo
      (parameters ⟨16,by decide⟩).whi (parameters ⟨16,by decide⟩).wE
      (parameters ⟨16,by decide⟩).o (parameters ⟨16,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass26W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e26W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num26C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨16,by decide⟩).clo
      (parameters ⟨16,by decide⟩).chi (parameters ⟨16,by decide⟩).cE
      (parameters ⟨16,by decide⟩).o (parameters ⟨16,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass26C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e26C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell26 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨16,by decide⟩)) :
    B (14735561841245226678488057 / 30000000000000000000000000) (9847696659323618469722501 / 20000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 26 ≤ θ at hl
  change θ ≤ noiseNode 27 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply26 : Supply (parameters ⟨16,by decide⟩)
    (cellLower (sourceIndex ⟨16,by decide⟩)) (cellUpper (sourceIndex ⟨16,by decide⟩)) := by
  refine ⟨valid16,num26W,num26C,?_,?_⟩
  · intro θ hθ
    exact (geometry26W (fullCell26 hθ)).1
  · intro θ hθ
    exact (geometry26C (fullCell26 hθ)).1

theorem radius26 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨16,by decide⟩).cRadius :=
  ⟨(geometry26W (fullCell26 hθ)).2,(geometry26C (fullCell26 hθ)).2⟩

theorem num27W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨17,by decide⟩).wlo
      (parameters ⟨17,by decide⟩).whi (parameters ⟨17,by decide⟩).wE
      (parameters ⟨17,by decide⟩).o (parameters ⟨17,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass27W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e27W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num27C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨17,by decide⟩).clo
      (parameters ⟨17,by decide⟩).chi (parameters ⟨17,by decide⟩).cE
      (parameters ⟨17,by decide⟩).o (parameters ⟨17,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass27C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e27C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell27 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨17,by decide⟩)) :
    B (9847696659323618469722501 / 20000000000000000000000000) (7403764068362814365339723 / 15000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 27 ≤ θ at hl
  change θ ≤ noiseNode 28 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply27 : Supply (parameters ⟨17,by decide⟩)
    (cellLower (sourceIndex ⟨17,by decide⟩)) (cellUpper (sourceIndex ⟨17,by decide⟩)) := by
  refine ⟨valid17,num27W,num27C,?_,?_⟩
  · intro θ hθ
    exact (geometry27W (fullCell27 hθ)).1
  · intro θ hθ
    exact (geometry27C (fullCell27 hθ)).1

theorem radius27 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨17,by decide⟩).cRadius :=
  ⟨(geometry27W (fullCell27 hθ)).2,(geometry27C (fullCell27 hθ)).2⟩

theorem num28W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨18,by decide⟩).wlo
      (parameters ⟨18,by decide⟩).whi (parameters ⟨18,by decide⟩).wE
      (parameters ⟨18,by decide⟩).o (parameters ⟨18,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass28W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e28W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num28C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨18,by decide⟩).clo
      (parameters ⟨18,by decide⟩).chi (parameters ⟨18,by decide⟩).cE
      (parameters ⟨18,by decide⟩).o (parameters ⟨18,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass28C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e28C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell28 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨18,by decide⟩)) :
    B (7403764068362814365339723 / 15000000000000000000000000) (29687022568931659513550281 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 28 ≤ θ at hl
  change θ ≤ noiseNode 29 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply28 : Supply (parameters ⟨18,by decide⟩)
    (cellLower (sourceIndex ⟨18,by decide⟩)) (cellUpper (sourceIndex ⟨18,by decide⟩)) := by
  refine ⟨valid18,num28W,num28C,?_,?_⟩
  · intro θ hθ
    exact (geometry28W (fullCell28 hθ)).1
  · intro θ hθ
    exact (geometry28C (fullCell28 hθ)).1

theorem radius28 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨18,by decide⟩).cRadius :=
  ⟨(geometry28W (fullCell28 hθ)).2,(geometry28C (fullCell28 hθ)).2⟩

theorem num29W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨19,by decide⟩).wlo
      (parameters ⟨19,by decide⟩).whi (parameters ⟨19,by decide⟩).wE
      (parameters ⟨19,by decide⟩).o (parameters ⟨19,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass29W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e29W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num29C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨19,by decide⟩).clo
      (parameters ⟨19,by decide⟩).chi (parameters ⟨19,by decide⟩).cE
      (parameters ⟨19,by decide⟩).o (parameters ⟨19,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass29C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e29C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell29 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨19,by decide⟩)) :
    B (29687022568931659513550281 / 60000000000000000000000000) (991966295480402052191389 / 2000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 29 ≤ θ at hl
  change θ ≤ noiseNode 30 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply29 : Supply (parameters ⟨19,by decide⟩)
    (cellLower (sourceIndex ⟨19,by decide⟩)) (cellUpper (sourceIndex ⟨19,by decide⟩)) := by
  refine ⟨valid19,num29W,num29C,?_,?_⟩
  · intro θ hθ
    exact (geometry29W (fullCell29 hθ)).1
  · intro θ hθ
    exact (geometry29C (fullCell29 hθ)).1

theorem radius29 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨19,by decide⟩).cRadius :=
  ⟨(geometry29W (fullCell29 hθ)).2,(geometry29C (fullCell29 hθ)).2⟩

theorem num30W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨20,by decide⟩).wlo
      (parameters ⟨20,by decide⟩).whi (parameters ⟨20,by decide⟩).wE
      (parameters ⟨20,by decide⟩).o (parameters ⟨20,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass30W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e30W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num30C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨20,by decide⟩).clo
      (parameters ⟨20,by decide⟩).chi (parameters ⟨20,by decide⟩).cE
      (parameters ⟨20,by decide⟩).o (parameters ⟨20,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass30C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e30C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell30 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨20,by decide⟩)) :
    B (991966295480402052191389 / 2000000000000000000000000) (29830955159892463617933059 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 30 ≤ θ at hl
  change θ ≤ noiseNode 31 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply30 : Supply (parameters ⟨20,by decide⟩)
    (cellLower (sourceIndex ⟨20,by decide⟩)) (cellUpper (sourceIndex ⟨20,by decide⟩)) := by
  refine ⟨valid20,num30W,num30C,?_,?_⟩
  · intro θ hθ
    exact (geometry30W (fullCell30 hθ)).1
  · intro θ hθ
    exact (geometry30C (fullCell30 hθ)).1

theorem radius30 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨20,by decide⟩).cRadius :=
  ⟨(geometry30W (fullCell30 hθ)).2,(geometry30C (fullCell30 hθ)).2⟩

theorem num31W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨21,by decide⟩).wlo
      (parameters ⟨21,by decide⟩).whi (parameters ⟨21,by decide⟩).wE
      (parameters ⟨21,by decide⟩).o (parameters ⟨21,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass31W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e31W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num31C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨21,by decide⟩).clo
      (parameters ⟨21,by decide⟩).chi (parameters ⟨21,by decide⟩).cE
      (parameters ⟨21,by decide⟩).o (parameters ⟨21,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass31C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e31C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell31 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨21,by decide⟩)) :
    B (29830955159892463617933059 / 60000000000000000000000000) (934466295480402052191389 / 1875000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 31 ≤ θ at hl
  change θ ≤ noiseNode 32 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply31 : Supply (parameters ⟨21,by decide⟩)
    (cellLower (sourceIndex ⟨21,by decide⟩)) (cellUpper (sourceIndex ⟨21,by decide⟩)) := by
  refine ⟨valid21,num31W,num31C,?_,?_⟩
  · intro θ hθ
    exact (geometry31W (fullCell31 hθ)).1
  · intro θ hθ
    exact (geometry31C (fullCell31 hθ)).1

theorem radius31 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨21,by decide⟩).cRadius :=
  ⟨(geometry31W (fullCell31 hθ)).2,(geometry31C (fullCell31 hθ)).2⟩

theorem num32W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨22,by decide⟩).wlo
      (parameters ⟨22,by decide⟩).whi (parameters ⟨22,by decide⟩).wE
      (parameters ⟨22,by decide⟩).o (parameters ⟨22,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass32W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e32W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num32C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨22,by decide⟩).clo
      (parameters ⟨22,by decide⟩).chi (parameters ⟨22,by decide⟩).cE
      (parameters ⟨22,by decide⟩).o (parameters ⟨22,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass32C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e32C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell32 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨22,by decide⟩)) :
    B (934466295480402052191389 / 1875000000000000000000000) (9991629250284422574105279 / 20000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 32 ≤ θ at hl
  change θ ≤ noiseNode 33 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply32 : Supply (parameters ⟨22,by decide⟩)
    (cellLower (sourceIndex ⟨22,by decide⟩)) (cellUpper (sourceIndex ⟨22,by decide⟩)) := by
  refine ⟨valid22,num32W,num32C,?_,?_⟩
  · intro θ hθ
    exact (geometry32W (fullCell32 hθ)).1
  · intro θ hθ
    exact (geometry32C (fullCell32 hθ)).1

theorem radius32 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨22,by decide⟩).cRadius :=
  ⟨(geometry32W (fullCell32 hθ)).2,(geometry32C (fullCell32 hθ)).2⟩

theorem num33W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨23,by decide⟩).wlo
      (parameters ⟨23,by decide⟩).whi (parameters ⟨23,by decide⟩).wE
      (parameters ⟨23,by decide⟩).o (parameters ⟨23,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass33W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e33W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num33C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨23,by decide⟩).clo
      (parameters ⟨23,by decide⟩).chi (parameters ⟨23,by decide⟩).cE
      (parameters ⟨23,by decide⟩).o (parameters ⟨23,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass33C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e33C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell33 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨23,by decide⟩)) :
    B (9991629250284422574105279 / 20000000000000000000000000) (15023427023166834887253613 / 30000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 33 ≤ θ at hl
  change θ ≤ noiseNode 34 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply33 : Supply (parameters ⟨23,by decide⟩)
    (cellLower (sourceIndex ⟨23,by decide⟩)) (cellUpper (sourceIndex ⟨23,by decide⟩)) := by
  refine ⟨valid23,num33W,num33C,?_,?_⟩
  · intro θ hθ
    exact (geometry33W (fullCell33 hθ)).1
  · intro θ hθ
    exact (geometry33C (fullCell33 hθ)).1

theorem radius33 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨23,by decide⟩).cRadius :=
  ⟨(geometry33W (fullCell33 hθ)).2,(geometry33C (fullCell33 hθ)).2⟩

theorem num34W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨24,by decide⟩).wlo
      (parameters ⟨24,by decide⟩).whi (parameters ⟨24,by decide⟩).wE
      (parameters ⟨24,by decide⟩).o (parameters ⟨24,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass34W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e34W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num34C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨24,by decide⟩).clo
      (parameters ⟨24,by decide⟩).chi (parameters ⟨24,by decide⟩).cE
      (parameters ⟨24,by decide⟩).o (parameters ⟨24,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass34C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e34C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell34 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨24,by decide⟩)) :
    B (15023427023166834887253613 / 30000000000000000000000000) (6023764068362814365339723 / 12000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 34 ≤ θ at hl
  change θ ≤ noiseNode 35 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply34 : Supply (parameters ⟨24,by decide⟩)
    (cellLower (sourceIndex ⟨24,by decide⟩)) (cellUpper (sourceIndex ⟨24,by decide⟩)) := by
  refine ⟨valid24,num34W,num34C,?_,?_⟩
  · intro θ hθ
    exact (geometry34W (fullCell34 hθ)).1
  · intro θ hθ
    exact (geometry34C (fullCell34 hθ)).1

theorem radius34 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨24,by decide⟩).cRadius :=
  ⟨(geometry34W (fullCell34 hθ)).2,(geometry34C (fullCell34 hθ)).2⟩

theorem num35W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨25,by decide⟩).wlo
      (parameters ⟨25,by decide⟩).whi (parameters ⟨25,by decide⟩).wE
      (parameters ⟨25,by decide⟩).o (parameters ⟨25,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass35W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e35W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num35C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨25,by decide⟩).clo
      (parameters ⟨25,by decide⟩).chi (parameters ⟨25,by decide⟩).cE
      (parameters ⟨25,by decide⟩).o (parameters ⟨25,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass35C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e35C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell35 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨25,by decide⟩)) :
    B (6023764068362814365339723 / 12000000000000000000000000) (2515898886441206156574167 / 5000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 35 ≤ θ at hl
  change θ ≤ noiseNode 36 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply35 : Supply (parameters ⟨25,by decide⟩)
    (cellLower (sourceIndex ⟨25,by decide⟩)) (cellUpper (sourceIndex ⟨25,by decide⟩)) := by
  refine ⟨valid25,num35W,num35C,?_,?_⟩
  · intro θ hθ
    exact (geometry35W (fullCell35 hθ)).1
  · intro θ hθ
    exact (geometry35C (fullCell35 hθ)).1

theorem radius35 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨25,by decide⟩).cRadius :=
  ⟨(geometry35W (fullCell35 hθ)).2,(geometry35C (fullCell35 hθ)).2⟩

theorem num36W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨26,by decide⟩).wlo
      (parameters ⟨26,by decide⟩).whi (parameters ⟨26,by decide⟩).wE
      (parameters ⟨26,by decide⟩).o (parameters ⟨26,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass36W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e36W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num36C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨26,by decide⟩).clo
      (parameters ⟨26,by decide⟩).chi (parameters ⟨26,by decide⟩).cE
      (parameters ⟨26,by decide⟩).o (parameters ⟨26,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass36C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e36C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell36 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨26,by decide⟩)) :
    B (2515898886441206156574167 / 5000000000000000000000000) (30262752932774875931081393 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 36 ≤ θ at hl
  change θ ≤ noiseNode 37 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply36 : Supply (parameters ⟨26,by decide⟩)
    (cellLower (sourceIndex ⟨26,by decide⟩)) (cellUpper (sourceIndex ⟨26,by decide⟩)) := by
  refine ⟨valid26,num36W,num36C,?_,?_⟩
  · intro θ hθ
    exact (geometry36W (fullCell36 hθ)).1
  · intro θ hθ
    exact (geometry36C (fullCell36 hθ)).1

theorem radius36 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨26,by decide⟩).cRadius :=
  ⟨(geometry36W (fullCell36 hθ)).2,(geometry36C (fullCell36 hθ)).2⟩

theorem num37W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨27,by decide⟩).wlo
      (parameters ⟨27,by decide⟩).whi (parameters ⟨27,by decide⟩).wE
      (parameters ⟨27,by decide⟩).o (parameters ⟨27,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass37W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e37W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num37C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨27,by decide⟩).clo
      (parameters ⟨27,by decide⟩).chi (parameters ⟨27,by decide⟩).cE
      (parameters ⟨27,by decide⟩).o (parameters ⟨27,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass37C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e37C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell37 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨27,by decide⟩)) :
    B (30262752932774875931081393 / 60000000000000000000000000) (15167359614127638991636391 / 30000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 37 ≤ θ at hl
  change θ ≤ noiseNode 38 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply37 : Supply (parameters ⟨27,by decide⟩)
    (cellLower (sourceIndex ⟨27,by decide⟩)) (cellUpper (sourceIndex ⟨27,by decide⟩)) := by
  refine ⟨valid27,num37W,num37C,?_,?_⟩
  · intro θ hθ
    exact (geometry37W (fullCell37 hθ)).1
  · intro θ hθ
    exact (geometry37C (fullCell37 hθ)).1

theorem radius37 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨27,by decide⟩).cRadius :=
  ⟨(geometry37W (fullCell37 hθ)).2,(geometry37C (fullCell37 hθ)).2⟩

theorem num38W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨28,by decide⟩).wlo
      (parameters ⟨28,by decide⟩).whi (parameters ⟨28,by decide⟩).wE
      (parameters ⟨28,by decide⟩).o (parameters ⟨28,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass38W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e38W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num38C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨28,by decide⟩).clo
      (parameters ⟨28,by decide⟩).chi (parameters ⟨28,by decide⟩).cE
      (parameters ⟨28,by decide⟩).o (parameters ⟨28,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass38C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e38C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell38 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨28,by decide⟩)) :
    B (15167359614127638991636391 / 30000000000000000000000000) (10135561841245226678488057 / 20000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 38 ≤ θ at hl
  change θ ≤ noiseNode 39 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply38 : Supply (parameters ⟨28,by decide⟩)
    (cellLower (sourceIndex ⟨28,by decide⟩)) (cellUpper (sourceIndex ⟨28,by decide⟩)) := by
  refine ⟨valid28,num38W,num38C,?_,?_⟩
  · intro θ hθ
    exact (geometry38W (fullCell38 hθ)).1
  · intro θ hθ
    exact (geometry38C (fullCell38 hθ)).1

theorem radius38 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨28,by decide⟩).cRadius :=
  ⟨(geometry38W (fullCell38 hθ)).2,(geometry38C (fullCell38 hθ)).2⟩

theorem num39W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨29,by decide⟩).wlo
      (parameters ⟨29,by decide⟩).whi (parameters ⟨29,by decide⟩).wE
      (parameters ⟨29,by decide⟩).o (parameters ⟨29,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass39W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e39W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num39C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨29,by decide⟩).clo
      (parameters ⟨29,by decide⟩).chi (parameters ⟨29,by decide⟩).cE
      (parameters ⟨29,by decide⟩).o (parameters ⟨29,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass39C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e39C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell39 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨29,by decide⟩)) :
    B (10135561841245226678488057 / 20000000000000000000000000) (761966295480402052191389 / 1500000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 39 ≤ θ at hl
  change θ ≤ noiseNode 40 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply39 : Supply (parameters ⟨29,by decide⟩)
    (cellLower (sourceIndex ⟨29,by decide⟩)) (cellUpper (sourceIndex ⟨29,by decide⟩)) := by
  refine ⟨valid29,num39W,num39C,?_,?_⟩
  · intro θ hθ
    exact (geometry39W (fullCell39 hθ)).1
  · intro θ hθ
    exact (geometry39C (fullCell39 hθ)).1

theorem radius39 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨29,by decide⟩).cRadius :=
  ⟨(geometry39W (fullCell39 hθ)).2,(geometry39C (fullCell39 hθ)).2⟩

theorem num40W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨30,by decide⟩).wlo
      (parameters ⟨30,by decide⟩).whi (parameters ⟨30,by decide⟩).wE
      (parameters ⟨30,by decide⟩).o (parameters ⟨30,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass40W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e40W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num40C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨30,by decide⟩).clo
      (parameters ⟨30,by decide⟩).chi (parameters ⟨30,by decide⟩).cE
      (parameters ⟨30,by decide⟩).o (parameters ⟨30,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass40C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e40C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell40 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨30,by decide⟩)) :
    B (761966295480402052191389 / 1500000000000000000000000) (30550618114696484139846949 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 40 ≤ θ at hl
  change θ ≤ noiseNode 41 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply40 : Supply (parameters ⟨30,by decide⟩)
    (cellLower (sourceIndex ⟨30,by decide⟩)) (cellUpper (sourceIndex ⟨30,by decide⟩)) := by
  refine ⟨valid30,num40W,num40C,?_,?_⟩
  · intro θ hθ
    exact (geometry40W (fullCell40 hθ)).1
  · intro θ hθ
    exact (geometry40C (fullCell40 hθ)).1

theorem radius40 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨30,by decide⟩).cRadius :=
  ⟨(geometry40W (fullCell40 hθ)).2,(geometry40C (fullCell40 hθ)).2⟩

theorem num41W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨31,by decide⟩).wlo
      (parameters ⟨31,by decide⟩).whi (parameters ⟨31,by decide⟩).wE
      (parameters ⟨31,by decide⟩).o (parameters ⟨31,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass41W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e41W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num41C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨31,by decide⟩).clo
      (parameters ⟨31,by decide⟩).chi (parameters ⟨31,by decide⟩).cE
      (parameters ⟨31,by decide⟩).o (parameters ⟨31,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass41C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e41C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell41 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨31,by decide⟩)) :
    B (30550618114696484139846949 / 60000000000000000000000000) (5103764068362814365339723 / 10000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 41 ≤ θ at hl
  change θ ≤ noiseNode 42 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply41 : Supply (parameters ⟨31,by decide⟩)
    (cellLower (sourceIndex ⟨31,by decide⟩)) (cellUpper (sourceIndex ⟨31,by decide⟩)) := by
  refine ⟨valid31,num41W,num41C,?_,?_⟩
  · intro θ hθ
    exact (geometry41W (fullCell41 hθ)).1
  · intro θ hθ
    exact (geometry41C (fullCell41 hθ)).1

theorem radius41 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨31,by decide⟩).cRadius :=
  ⟨(geometry41W (fullCell41 hθ)).2,(geometry41C (fullCell41 hθ)).2⟩

theorem num42W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨32,by decide⟩).wlo
      (parameters ⟨32,by decide⟩).whi (parameters ⟨32,by decide⟩).wE
      (parameters ⟨32,by decide⟩).o (parameters ⟨32,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass42W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e42W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num42C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨32,by decide⟩).clo
      (parameters ⟨32,by decide⟩).chi (parameters ⟨32,by decide⟩).cE
      (parameters ⟨32,by decide⟩).o (parameters ⟨32,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass42C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e42C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell42 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨32,by decide⟩)) :
    B (5103764068362814365339723 / 10000000000000000000000000) (30694550705657288244229727 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 42 ≤ θ at hl
  change θ ≤ noiseNode 43 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply42 : Supply (parameters ⟨32,by decide⟩)
    (cellLower (sourceIndex ⟨32,by decide⟩)) (cellUpper (sourceIndex ⟨32,by decide⟩)) := by
  refine ⟨valid32,num42W,num42C,?_,?_⟩
  · intro θ hθ
    exact (geometry42W (fullCell42 hθ)).1
  · intro θ hθ
    exact (geometry42C (fullCell42 hθ)).1

theorem radius42 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨32,by decide⟩).cRadius :=
  ⟨(geometry42W (fullCell42 hθ)).2,(geometry42C (fullCell42 hθ)).2⟩

theorem num43W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨33,by decide⟩).wlo
      (parameters ⟨33,by decide⟩).whi (parameters ⟨33,by decide⟩).wE
      (parameters ⟨33,by decide⟩).o (parameters ⟨33,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass43W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e43W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num43C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨33,by decide⟩).clo
      (parameters ⟨33,by decide⟩).chi (parameters ⟨33,by decide⟩).cE
      (parameters ⟨33,by decide⟩).o (parameters ⟨33,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass43C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e43C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell43 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨33,by decide⟩)) :
    B (30694550705657288244229727 / 60000000000000000000000000) (7691629250284422574105279 / 15000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 43 ≤ θ at hl
  change θ ≤ noiseNode 44 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply43 : Supply (parameters ⟨33,by decide⟩)
    (cellLower (sourceIndex ⟨33,by decide⟩)) (cellUpper (sourceIndex ⟨33,by decide⟩)) := by
  refine ⟨valid33,num43W,num43C,?_,?_⟩
  · intro θ hθ
    exact (geometry43W (fullCell43 hθ)).1
  · intro θ hθ
    exact (geometry43C (fullCell43 hθ)).1

theorem radius43 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨33,by decide⟩).cRadius :=
  ⟨(geometry43W (fullCell43 hθ)).2,(geometry43C (fullCell43 hθ)).2⟩

theorem num44W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨34,by decide⟩).wlo
      (parameters ⟨34,by decide⟩).whi (parameters ⟨34,by decide⟩).wE
      (parameters ⟨34,by decide⟩).o (parameters ⟨34,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass44W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e44W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num44C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨34,by decide⟩).clo
      (parameters ⟨34,by decide⟩).chi (parameters ⟨34,by decide⟩).cE
      (parameters ⟨34,by decide⟩).o (parameters ⟨34,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass44C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e44C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell44 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨34,by decide⟩)) :
    B (7691629250284422574105279 / 15000000000000000000000000) (2055898886441206156574167 / 4000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 44 ≤ θ at hl
  change θ ≤ noiseNode 45 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply44 : Supply (parameters ⟨34,by decide⟩)
    (cellLower (sourceIndex ⟨34,by decide⟩)) (cellUpper (sourceIndex ⟨34,by decide⟩)) := by
  refine ⟨valid34,num44W,num44C,?_,?_⟩
  · intro θ hθ
    exact (geometry44W (fullCell44 hθ)).1
  · intro θ hθ
    exact (geometry44C (fullCell44 hθ)).1

theorem radius44 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨34,by decide⟩).cRadius :=
  ⟨(geometry44W (fullCell44 hθ)).2,(geometry44C (fullCell44 hθ)).2⟩

theorem num45W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨35,by decide⟩).wlo
      (parameters ⟨35,by decide⟩).whi (parameters ⟨35,by decide⟩).wE
      (parameters ⟨35,by decide⟩).o (parameters ⟨35,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass45W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e45W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num45C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨35,by decide⟩).clo
      (parameters ⟨35,by decide⟩).chi (parameters ⟨35,by decide⟩).cE
      (parameters ⟨35,by decide⟩).o (parameters ⟨35,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass45C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e45C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell45 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨35,by decide⟩)) :
    B (2055898886441206156574167 / 4000000000000000000000000) (15455224796049247200401947 / 30000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 45 ≤ θ at hl
  change θ ≤ noiseNode 46 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply45 : Supply (parameters ⟨35,by decide⟩)
    (cellLower (sourceIndex ⟨35,by decide⟩)) (cellUpper (sourceIndex ⟨35,by decide⟩)) := by
  refine ⟨valid35,num45W,num45C,?_,?_⟩
  · intro θ hθ
    exact (geometry45W (fullCell45 hθ)).1
  · intro θ hθ
    exact (geometry45C (fullCell45 hθ)).1

theorem radius45 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨35,by decide⟩).cRadius :=
  ⟨(geometry45W (fullCell45 hθ)).2,(geometry45C (fullCell45 hθ)).2⟩

theorem num46W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨36,by decide⟩).wlo
      (parameters ⟨36,by decide⟩).whi (parameters ⟨36,by decide⟩).wE
      (parameters ⟨36,by decide⟩).o (parameters ⟨36,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass46W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e46W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num46C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨36,by decide⟩).clo
      (parameters ⟨36,by decide⟩).chi (parameters ⟨36,by decide⟩).cE
      (parameters ⟨36,by decide⟩).o (parameters ⟨36,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass46C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e46C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell46 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨36,by decide⟩)) :
    B (15455224796049247200401947 / 30000000000000000000000000) (30982415887578896452995283 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 46 ≤ θ at hl
  change θ ≤ noiseNode 47 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply46 : Supply (parameters ⟨36,by decide⟩)
    (cellLower (sourceIndex ⟨36,by decide⟩)) (cellUpper (sourceIndex ⟨36,by decide⟩)) := by
  refine ⟨valid36,num46W,num46C,?_,?_⟩
  · intro θ hθ
    exact (geometry46W (fullCell46 hθ)).1
  · intro θ hθ
    exact (geometry46C (fullCell46 hθ)).1

theorem radius46 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨36,by decide⟩).cRadius :=
  ⟨(geometry46W (fullCell46 hθ)).2,(geometry46C (fullCell46 hθ)).2⟩

theorem num47W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨37,by decide⟩).wlo
      (parameters ⟨37,by decide⟩).whi (parameters ⟨37,by decide⟩).wE
      (parameters ⟨37,by decide⟩).o (parameters ⟨37,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass47W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e47W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num47C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨37,by decide⟩).clo
      (parameters ⟨37,by decide⟩).chi (parameters ⟨37,by decide⟩).cE
      (parameters ⟨37,by decide⟩).o (parameters ⟨37,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass47C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e47C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell47 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨37,by decide⟩)) :
    B (30982415887578896452995283 / 60000000000000000000000000) (646966295480402052191389 / 1250000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 47 ≤ θ at hl
  change θ ≤ noiseNode 48 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply47 : Supply (parameters ⟨37,by decide⟩)
    (cellLower (sourceIndex ⟨37,by decide⟩)) (cellUpper (sourceIndex ⟨37,by decide⟩)) := by
  refine ⟨valid37,num47W,num47C,?_,?_⟩
  · intro θ hθ
    exact (geometry47W (fullCell47 hθ)).1
  · intro θ hθ
    exact (geometry47C (fullCell47 hθ)).1

theorem radius47 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨37,by decide⟩).cRadius :=
  ⟨(geometry47W (fullCell47 hθ)).2,(geometry47C (fullCell47 hθ)).2⟩

theorem num48W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨38,by decide⟩).wlo
      (parameters ⟨38,by decide⟩).whi (parameters ⟨38,by decide⟩).wE
      (parameters ⟨38,by decide⟩).o (parameters ⟨38,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass48W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e48W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num48C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨38,by decide⟩).clo
      (parameters ⟨38,by decide⟩).chi (parameters ⟨38,by decide⟩).cE
      (parameters ⟨38,by decide⟩).o (parameters ⟨38,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass48C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e48C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell48 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨38,by decide⟩)) :
    B (646966295480402052191389 / 1250000000000000000000000) (31126348478539700557378061 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 48 ≤ θ at hl
  change θ ≤ noiseNode 49 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply48 : Supply (parameters ⟨38,by decide⟩)
    (cellLower (sourceIndex ⟨38,by decide⟩)) (cellUpper (sourceIndex ⟨38,by decide⟩)) := by
  refine ⟨valid38,num48W,num48C,?_,?_⟩
  · intro θ hθ
    exact (geometry48W (fullCell48 hθ)).1
  · intro θ hθ
    exact (geometry48C (fullCell48 hθ)).1

theorem radius48 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨38,by decide⟩).cRadius :=
  ⟨(geometry48W (fullCell48 hθ)).2,(geometry48C (fullCell48 hθ)).2⟩

theorem num49W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨39,by decide⟩).wlo
      (parameters ⟨39,by decide⟩).whi (parameters ⟨39,by decide⟩).wE
      (parameters ⟨39,by decide⟩).o (parameters ⟨39,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass49W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e49W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num49C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨39,by decide⟩).clo
      (parameters ⟨39,by decide⟩).chi (parameters ⟨39,by decide⟩).cE
      (parameters ⟨39,by decide⟩).o (parameters ⟨39,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass49C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e49C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell49 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨39,by decide⟩)) :
    B (31126348478539700557378061 / 60000000000000000000000000) (623966295480402052191389 / 1200000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 49 ≤ θ at hl
  change θ ≤ noiseNode 50 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply49 : Supply (parameters ⟨39,by decide⟩)
    (cellLower (sourceIndex ⟨39,by decide⟩)) (cellUpper (sourceIndex ⟨39,by decide⟩)) := by
  refine ⟨valid39,num49W,num49C,?_,?_⟩
  · intro θ hθ
    exact (geometry49W (fullCell49 hθ)).1
  · intro θ hθ
    exact (geometry49C (fullCell49 hθ)).1

theorem radius49 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨39,by decide⟩).cRadius :=
  ⟨(geometry49W (fullCell49 hθ)).2,(geometry49C (fullCell49 hθ)).2⟩

theorem num50W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨40,by decide⟩).wlo
      (parameters ⟨40,by decide⟩).whi (parameters ⟨40,by decide⟩).wE
      (parameters ⟨40,by decide⟩).o (parameters ⟨40,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass50W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e50W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num50C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨40,by decide⟩).clo
      (parameters ⟨40,by decide⟩).chi (parameters ⟨40,by decide⟩).cE
      (parameters ⟨40,by decide⟩).o (parameters ⟨40,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass50C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e50C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell50 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨40,by decide⟩)) :
    B (623966295480402052191389 / 1200000000000000000000000) (10423427023166834887253613 / 20000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 50 ≤ θ at hl
  change θ ≤ noiseNode 51 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply50 : Supply (parameters ⟨40,by decide⟩)
    (cellLower (sourceIndex ⟨40,by decide⟩)) (cellUpper (sourceIndex ⟨40,by decide⟩)) := by
  refine ⟨valid40,num50W,num50C,?_,?_⟩
  · intro θ hθ
    exact (geometry50W (fullCell50 hθ)).1
  · intro θ hθ
    exact (geometry50C (fullCell50 hθ)).1

theorem radius50 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨40,by decide⟩).cRadius :=
  ⟨(geometry50W (fullCell50 hθ)).2,(geometry50C (fullCell50 hθ)).2⟩

theorem num51W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨41,by decide⟩).wlo
      (parameters ⟨41,by decide⟩).whi (parameters ⟨41,by decide⟩).wE
      (parameters ⟨41,by decide⟩).o (parameters ⟨41,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass51W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e51W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num51C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨41,by decide⟩).clo
      (parameters ⟨41,by decide⟩).chi (parameters ⟨41,by decide⟩).cE
      (parameters ⟨41,by decide⟩).o (parameters ⟨41,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass51C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e51C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell51 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨41,by decide⟩)) :
    B (10423427023166834887253613 / 20000000000000000000000000) (7835561841245226678488057 / 15000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 51 ≤ θ at hl
  change θ ≤ noiseNode 52 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply51 : Supply (parameters ⟨41,by decide⟩)
    (cellLower (sourceIndex ⟨41,by decide⟩)) (cellUpper (sourceIndex ⟨41,by decide⟩)) := by
  refine ⟨valid41,num51W,num51C,?_,?_⟩
  · intro θ hθ
    exact (geometry51W (fullCell51 hθ)).1
  · intro θ hθ
    exact (geometry51C (fullCell51 hθ)).1

theorem radius51 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨41,by decide⟩).cRadius :=
  ⟨(geometry51W (fullCell51 hθ)).2,(geometry51C (fullCell51 hθ)).2⟩

theorem num52W :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨42,by decide⟩).wlo
      (parameters ⟨42,by decide⟩).whi (parameters ⟨42,by decide⟩).wE
      (parameters ⟨42,by decide⟩).o (parameters ⟨42,by decide⟩).wS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass52W (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e52W ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem num52C :
    BstLean.Part246.ta_num_sharp 12225 (parameters ⟨42,by decide⟩).clo
      (parameters ⟨42,by decide⟩).chi (parameters ⟨42,by decide⟩).cE
      (parameters ⟨42,by decide⟩).o (parameters ⟨42,by decide⟩).cS maskSlack 46 := by
  refine ⟨by convert o_bound using 1 <;> norm_num [parameters],am_positive,?_⟩
  intro c hlo hhi
  have hs := sClass52C (c := c) ⟨hlo,hhi⟩
  exact ⟨hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,hs.2.2.2.2.2.1,
    e52C ⟨hlo,hhi⟩,hs.2.2.2.2.2.2⟩

theorem fullCell52 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨42,by decide⟩)) :
    B (7835561841245226678488057 / 15000000000000000000000000) (31414213660461308766143617 / 60000000000000000000000000) θ := by
  have hl := (le_max_left _ _).trans hθ.1
  have hu := hθ.2.trans (min_le_left _ _)
  change noiseNode 52 ≤ θ at hl
  change θ ≤ noiseNode 53 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩

theorem supply52 : Supply (parameters ⟨42,by decide⟩)
    (cellLower (sourceIndex ⟨42,by decide⟩)) (cellUpper (sourceIndex ⟨42,by decide⟩)) := by
  refine ⟨valid42,num52W,num52C,?_,?_⟩
  · intro θ hθ
    exact (geometry52W (fullCell52 hθ)).1
  · intro θ hθ
    exact (geometry52C (fullCell52 hθ)).1

theorem radius52 {θ : ℝ} (hθ : θ ∈ cell (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨42,by decide⟩).cRadius :=
  ⟨(geometry52W (fullCell52 hθ)).2,(geometry52C (fullCell52 hθ)).2⟩

theorem supplies (j : Fin 43) : Supply (parameters j)
    (cellLower (sourceIndex j)) (cellUpper (sourceIndex j)) := by
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

theorem radii (j : Fin 43) {θ : ℝ} (hθ : θ ∈ cell (sourceIndex j)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤ (parameters j).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤ (parameters j).cRadius := by
  match j with
  | ⟨0,_⟩ => exact radius10 hθ
  | ⟨1,_⟩ => exact radius11 hθ
  | ⟨2,_⟩ => exact radius12 hθ
  | ⟨3,_⟩ => exact radius13 hθ
  | ⟨4,_⟩ => exact radius14 hθ
  | ⟨5,_⟩ => exact radius15 hθ
  | ⟨6,_⟩ => exact radius16 hθ
  | ⟨7,_⟩ => exact radius17 hθ
  | ⟨8,_⟩ => exact radius18 hθ
  | ⟨9,_⟩ => exact radius19 hθ
  | ⟨10,_⟩ => exact radius20 hθ
  | ⟨11,_⟩ => exact radius21 hθ
  | ⟨12,_⟩ => exact radius22 hθ
  | ⟨13,_⟩ => exact radius23 hθ
  | ⟨14,_⟩ => exact radius24 hθ
  | ⟨15,_⟩ => exact radius25 hθ
  | ⟨16,_⟩ => exact radius26 hθ
  | ⟨17,_⟩ => exact radius27 hθ
  | ⟨18,_⟩ => exact radius28 hθ
  | ⟨19,_⟩ => exact radius29 hθ
  | ⟨20,_⟩ => exact radius30 hθ
  | ⟨21,_⟩ => exact radius31 hθ
  | ⟨22,_⟩ => exact radius32 hθ
  | ⟨23,_⟩ => exact radius33 hθ
  | ⟨24,_⟩ => exact radius34 hθ
  | ⟨25,_⟩ => exact radius35 hθ
  | ⟨26,_⟩ => exact radius36 hθ
  | ⟨27,_⟩ => exact radius37 hθ
  | ⟨28,_⟩ => exact radius38 hθ
  | ⟨29,_⟩ => exact radius39 hθ
  | ⟨30,_⟩ => exact radius40 hθ
  | ⟨31,_⟩ => exact radius41 hθ
  | ⟨32,_⟩ => exact radius42 hθ
  | ⟨33,_⟩ => exact radius43 hθ
  | ⟨34,_⟩ => exact radius44 hθ
  | ⟨35,_⟩ => exact radius45 hθ
  | ⟨36,_⟩ => exact radius46 hθ
  | ⟨37,_⟩ => exact radius47 hθ
  | ⟨38,_⟩ => exact radius48 hθ
  | ⟨39,_⟩ => exact radius49 hθ
  | ⟨40,_⟩ => exact radius50 hθ
  | ⟨41,_⟩ => exact radius51 hθ
  | ⟨42,_⟩ => exact radius52 hθ
  | ⟨j+43,h⟩ => exact False.elim (by omega)

theorem selected_payment (D : BstLean.Part157.Design 12225)
    (hτW : BstLean.Part160.TauWorld D) :
    (BstLean.Part157.retDist D.toCentres).real
      (BstLean.Part160.agentEv D (selected parameters payment))ᶜ ≤ (1/4000 : ℝ) :=
  selected_charge parameters supplies D hτW (by norm_num [payment])

theorem selected_paper_cutoff_payment (D : BstLean.Part157.Design 12225)
    (hτW : BstLean.Part160.TauWorld D) :
    (BstLean.Part157.retDist D.toCentres).real
      (BstLean.Part160.agentEv D (selected parameters sourcePayment))ᶜ ≤ (13/40000 : ℝ) :=
  selected_charge parameters supplies D hτW (by norm_num [sourcePayment])

end BstLean.Part255
