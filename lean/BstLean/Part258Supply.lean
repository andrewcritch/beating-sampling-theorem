import BstLean.Part258Selection
import BstLean.Part255Supply

namespace BstLean.Part258
open Real Set BstLean.Part182 BstLean.Part255
open BstLean.Part251 (noiseNode proposedThetaUpper)

theorem fullCell10 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨0,by decide⟩)) :
    B (2831966295480402052191389 / 6000000000000000000000000) (28391629250284422574105279 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 10 ≤ θ at hl
  change θ ≤ noiseNode 11 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply10 : Supply (parameters ⟨0,by decide⟩)
    (sourceLower (sourceIndex ⟨0,by decide⟩)) (sourceUpper (sourceIndex ⟨0,by decide⟩)) := by
  refine ⟨valid0,num10W,num10C,?_,?_⟩
  · intro θ hθ
    exact (geometry10W (fullCell10 hθ)).1
  · intro θ hθ
    exact (geometry10C (fullCell10 hθ)).1


theorem radius10 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨0,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨0,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨0,by decide⟩).cRadius :=
  ⟨(geometry10W (fullCell10 hθ)).2,(geometry10C (fullCell10 hθ)).2⟩


theorem fullCell11 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨1,by decide⟩)) :
    B (28391629250284422574105279 / 60000000000000000000000000) (2371966295480402052191389 / 5000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 11 ≤ θ at hl
  change θ ≤ noiseNode 12 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply11 : Supply (parameters ⟨1,by decide⟩)
    (sourceLower (sourceIndex ⟨1,by decide⟩)) (sourceUpper (sourceIndex ⟨1,by decide⟩)) := by
  refine ⟨valid1,num11W,num11C,?_,?_⟩
  · intro θ hθ
    exact (geometry11W (fullCell11 hθ)).1
  · intro θ hθ
    exact (geometry11C (fullCell11 hθ)).1


theorem radius11 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨1,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨1,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨1,by decide⟩).cRadius :=
  ⟨(geometry11W (fullCell11 hθ)).2,(geometry11C (fullCell11 hθ)).2⟩


theorem fullCell12 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨2,by decide⟩)) :
    B (2371966295480402052191389 / 5000000000000000000000000) (28535561841245226678488057 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 12 ≤ θ at hl
  change θ ≤ noiseNode 13 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply12 : Supply (parameters ⟨2,by decide⟩)
    (sourceLower (sourceIndex ⟨2,by decide⟩)) (sourceUpper (sourceIndex ⟨2,by decide⟩)) := by
  refine ⟨valid2,num12W,num12C,?_,?_⟩
  · intro θ hθ
    exact (geometry12W (fullCell12 hθ)).1
  · intro θ hθ
    exact (geometry12C (fullCell12 hθ)).1


theorem radius12 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨2,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨2,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨2,by decide⟩).cRadius :=
  ⟨(geometry12W (fullCell12 hθ)).2,(geometry12C (fullCell12 hθ)).2⟩


theorem fullCell13 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨3,by decide⟩)) :
    B (28535561841245226678488057 / 60000000000000000000000000) (14303764068362814365339723 / 30000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 13 ≤ θ at hl
  change θ ≤ noiseNode 14 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply13 : Supply (parameters ⟨3,by decide⟩)
    (sourceLower (sourceIndex ⟨3,by decide⟩)) (sourceUpper (sourceIndex ⟨3,by decide⟩)) := by
  refine ⟨valid3,num13W,num13C,?_,?_⟩
  · intro θ hθ
    exact (geometry13W (fullCell13 hθ)).1
  · intro θ hθ
    exact (geometry13C (fullCell13 hθ)).1


theorem radius13 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨3,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨3,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨3,by decide⟩).cRadius :=
  ⟨(geometry13W (fullCell13 hθ)).2,(geometry13C (fullCell13 hθ)).2⟩


theorem fullCell14 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨4,by decide⟩)) :
    B (14303764068362814365339723 / 30000000000000000000000000) (1911966295480402052191389 / 4000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 14 ≤ θ at hl
  change θ ≤ noiseNode 15 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply14 : Supply (parameters ⟨4,by decide⟩)
    (sourceLower (sourceIndex ⟨4,by decide⟩)) (sourceUpper (sourceIndex ⟨4,by decide⟩)) := by
  refine ⟨valid4,num14W,num14C,?_,?_⟩
  · intro θ hθ
    exact (geometry14W (fullCell14 hθ)).1
  · intro θ hθ
    exact (geometry14C (fullCell14 hθ)).1


theorem radius14 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨4,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨4,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨4,by decide⟩).cRadius :=
  ⟨(geometry14W (fullCell14 hθ)).2,(geometry14C (fullCell14 hθ)).2⟩


theorem fullCell15 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨5,by decide⟩)) :
    B (1911966295480402052191389 / 4000000000000000000000000) (1796966295480402052191389 / 3750000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 15 ≤ θ at hl
  change θ ≤ noiseNode 16 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply15 : Supply (parameters ⟨5,by decide⟩)
    (sourceLower (sourceIndex ⟨5,by decide⟩)) (sourceUpper (sourceIndex ⟨5,by decide⟩)) := by
  refine ⟨valid5,num15W,num15C,?_,?_⟩
  · intro θ hθ
    exact (geometry15W (fullCell15 hθ)).1
  · intro θ hθ
    exact (geometry15C (fullCell15 hθ)).1


theorem radius15 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨5,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨5,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨5,by decide⟩).cRadius :=
  ⟨(geometry15W (fullCell15 hθ)).2,(geometry15C (fullCell15 hθ)).2⟩


theorem fullCell16 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨6,by decide⟩)) :
    B (1796966295480402052191389 / 3750000000000000000000000) (28823427023166834887253613 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 16 ≤ θ at hl
  change θ ≤ noiseNode 17 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply16 : Supply (parameters ⟨6,by decide⟩)
    (sourceLower (sourceIndex ⟨6,by decide⟩)) (sourceUpper (sourceIndex ⟨6,by decide⟩)) := by
  refine ⟨valid6,num16W,num16C,?_,?_⟩
  · intro θ hθ
    exact (geometry16W (fullCell16 hθ)).1
  · intro θ hθ
    exact (geometry16C (fullCell16 hθ)).1


theorem radius16 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨6,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨6,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨6,by decide⟩).cRadius :=
  ⟨(geometry16W (fullCell16 hθ)).2,(geometry16C (fullCell16 hθ)).2⟩


theorem fullCell17 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨7,by decide⟩)) :
    B (28823427023166834887253613 / 60000000000000000000000000) (4815898886441206156574167 / 10000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 17 ≤ θ at hl
  change θ ≤ noiseNode 18 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply17 : Supply (parameters ⟨7,by decide⟩)
    (sourceLower (sourceIndex ⟨7,by decide⟩)) (sourceUpper (sourceIndex ⟨7,by decide⟩)) := by
  refine ⟨valid7,num17W,num17C,?_,?_⟩
  · intro θ hθ
    exact (geometry17W (fullCell17 hθ)).1
  · intro θ hθ
    exact (geometry17C (fullCell17 hθ)).1


theorem radius17 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨7,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨7,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨7,by decide⟩).cRadius :=
  ⟨(geometry17W (fullCell17 hθ)).2,(geometry17C (fullCell17 hθ)).2⟩


theorem fullCell18 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨8,by decide⟩)) :
    B (4815898886441206156574167 / 10000000000000000000000000) (28967359614127638991636391 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 18 ≤ θ at hl
  change θ ≤ noiseNode 19 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply18 : Supply (parameters ⟨8,by decide⟩)
    (sourceLower (sourceIndex ⟨8,by decide⟩)) (sourceUpper (sourceIndex ⟨8,by decide⟩)) := by
  refine ⟨valid8,num18W,num18C,?_,?_⟩
  · intro θ hθ
    exact (geometry18W (fullCell18 hθ)).1
  · intro θ hθ
    exact (geometry18C (fullCell18 hθ)).1


theorem radius18 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨8,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨8,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨8,by decide⟩).cRadius :=
  ⟨(geometry18W (fullCell18 hθ)).2,(geometry18C (fullCell18 hθ)).2⟩


theorem fullCell19 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨9,by decide⟩)) :
    B (28967359614127638991636391 / 60000000000000000000000000) (1451966295480402052191389 / 3000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 19 ≤ θ at hl
  change θ ≤ noiseNode 20 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply19 : Supply (parameters ⟨9,by decide⟩)
    (sourceLower (sourceIndex ⟨9,by decide⟩)) (sourceUpper (sourceIndex ⟨9,by decide⟩)) := by
  refine ⟨valid9,num19W,num19C,?_,?_⟩
  · intro θ hθ
    exact (geometry19W (fullCell19 hθ)).1
  · intro θ hθ
    exact (geometry19C (fullCell19 hθ)).1


theorem radius19 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨9,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨9,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨9,by decide⟩).cRadius :=
  ⟨(geometry19W (fullCell19 hθ)).2,(geometry19C (fullCell19 hθ)).2⟩


theorem fullCell20 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨10,by decide⟩)) :
    B (1451966295480402052191389 / 3000000000000000000000000) (9703764068362814365339723 / 20000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 20 ≤ θ at hl
  change θ ≤ noiseNode 21 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply20 : Supply (parameters ⟨10,by decide⟩)
    (sourceLower (sourceIndex ⟨10,by decide⟩)) (sourceUpper (sourceIndex ⟨10,by decide⟩)) := by
  refine ⟨valid10,num20W,num20C,?_,?_⟩
  · intro θ hθ
    exact (geometry20W (fullCell20 hθ)).1
  · intro θ hθ
    exact (geometry20C (fullCell20 hθ)).1


theorem radius20 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨10,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨10,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨10,by decide⟩).cRadius :=
  ⟨(geometry20W (fullCell20 hθ)).2,(geometry20C (fullCell20 hθ)).2⟩


theorem fullCell21 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨11,by decide⟩)) :
    B (9703764068362814365339723 / 20000000000000000000000000) (14591629250284422574105279 / 30000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 21 ≤ θ at hl
  change θ ≤ noiseNode 22 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply21 : Supply (parameters ⟨11,by decide⟩)
    (sourceLower (sourceIndex ⟨11,by decide⟩)) (sourceUpper (sourceIndex ⟨11,by decide⟩)) := by
  refine ⟨valid11,num21W,num21C,?_,?_⟩
  · intro θ hθ
    exact (geometry21W (fullCell21 hθ)).1
  · intro θ hθ
    exact (geometry21C (fullCell21 hθ)).1


theorem radius21 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨11,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨11,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨11,by decide⟩).cRadius :=
  ⟨(geometry21W (fullCell21 hθ)).2,(geometry21C (fullCell21 hθ)).2⟩


theorem fullCell22 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨12,by decide⟩)) :
    B (14591629250284422574105279 / 30000000000000000000000000) (29255224796049247200401947 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 22 ≤ θ at hl
  change θ ≤ noiseNode 23 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply22 : Supply (parameters ⟨12,by decide⟩)
    (sourceLower (sourceIndex ⟨12,by decide⟩)) (sourceUpper (sourceIndex ⟨12,by decide⟩)) := by
  refine ⟨valid12,num22W,num22C,?_,?_⟩
  · intro θ hθ
    exact (geometry22W (fullCell22 hθ)).1
  · intro θ hθ
    exact (geometry22C (fullCell22 hθ)).1


theorem radius22 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨12,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨12,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨12,by decide⟩).cRadius :=
  ⟨(geometry22W (fullCell22 hθ)).2,(geometry22C (fullCell22 hθ)).2⟩


theorem fullCell23 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨13,by decide⟩)) :
    B (29255224796049247200401947 / 60000000000000000000000000) (1221966295480402052191389 / 2500000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 23 ≤ θ at hl
  change θ ≤ noiseNode 24 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply23 : Supply (parameters ⟨13,by decide⟩)
    (sourceLower (sourceIndex ⟨13,by decide⟩)) (sourceUpper (sourceIndex ⟨13,by decide⟩)) := by
  refine ⟨valid13,num23W,num23C,?_,?_⟩
  · intro θ hθ
    exact (geometry23W (fullCell23 hθ)).1
  · intro θ hθ
    exact (geometry23C (fullCell23 hθ)).1


theorem radius23 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨13,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨13,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨13,by decide⟩).cRadius :=
  ⟨(geometry23W (fullCell23 hθ)).2,(geometry23C (fullCell23 hθ)).2⟩


theorem fullCell24 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨14,by decide⟩)) :
    B (1221966295480402052191389 / 2500000000000000000000000) (1175966295480402052191389 / 2400000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 24 ≤ θ at hl
  change θ ≤ noiseNode 25 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply24 : Supply (parameters ⟨14,by decide⟩)
    (sourceLower (sourceIndex ⟨14,by decide⟩)) (sourceUpper (sourceIndex ⟨14,by decide⟩)) := by
  refine ⟨valid14,num24W,num24C,?_,?_⟩
  · intro θ hθ
    exact (geometry24W (fullCell24 hθ)).1
  · intro θ hθ
    exact (geometry24C (fullCell24 hθ)).1


theorem radius24 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨14,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨14,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨14,by decide⟩).cRadius :=
  ⟨(geometry24W (fullCell24 hθ)).2,(geometry24C (fullCell24 hθ)).2⟩


theorem fullCell25 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨15,by decide⟩)) :
    B (1175966295480402052191389 / 2400000000000000000000000) (14735561841245226678488057 / 30000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 25 ≤ θ at hl
  change θ ≤ noiseNode 26 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply25 : Supply (parameters ⟨15,by decide⟩)
    (sourceLower (sourceIndex ⟨15,by decide⟩)) (sourceUpper (sourceIndex ⟨15,by decide⟩)) := by
  refine ⟨valid15,num25W,num25C,?_,?_⟩
  · intro θ hθ
    exact (geometry25W (fullCell25 hθ)).1
  · intro θ hθ
    exact (geometry25C (fullCell25 hθ)).1


theorem radius25 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨15,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨15,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨15,by decide⟩).cRadius :=
  ⟨(geometry25W (fullCell25 hθ)).2,(geometry25C (fullCell25 hθ)).2⟩


theorem fullCell26 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨16,by decide⟩)) :
    B (14735561841245226678488057 / 30000000000000000000000000) (9847696659323618469722501 / 20000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 26 ≤ θ at hl
  change θ ≤ noiseNode 27 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply26 : Supply (parameters ⟨16,by decide⟩)
    (sourceLower (sourceIndex ⟨16,by decide⟩)) (sourceUpper (sourceIndex ⟨16,by decide⟩)) := by
  refine ⟨valid16,num26W,num26C,?_,?_⟩
  · intro θ hθ
    exact (geometry26W (fullCell26 hθ)).1
  · intro θ hθ
    exact (geometry26C (fullCell26 hθ)).1


theorem radius26 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨16,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨16,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨16,by decide⟩).cRadius :=
  ⟨(geometry26W (fullCell26 hθ)).2,(geometry26C (fullCell26 hθ)).2⟩


theorem fullCell27 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨17,by decide⟩)) :
    B (9847696659323618469722501 / 20000000000000000000000000) (7403764068362814365339723 / 15000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 27 ≤ θ at hl
  change θ ≤ noiseNode 28 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply27 : Supply (parameters ⟨17,by decide⟩)
    (sourceLower (sourceIndex ⟨17,by decide⟩)) (sourceUpper (sourceIndex ⟨17,by decide⟩)) := by
  refine ⟨valid17,num27W,num27C,?_,?_⟩
  · intro θ hθ
    exact (geometry27W (fullCell27 hθ)).1
  · intro θ hθ
    exact (geometry27C (fullCell27 hθ)).1


theorem radius27 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨17,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨17,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨17,by decide⟩).cRadius :=
  ⟨(geometry27W (fullCell27 hθ)).2,(geometry27C (fullCell27 hθ)).2⟩


theorem fullCell28 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨18,by decide⟩)) :
    B (7403764068362814365339723 / 15000000000000000000000000) (29687022568931659513550281 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 28 ≤ θ at hl
  change θ ≤ noiseNode 29 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply28 : Supply (parameters ⟨18,by decide⟩)
    (sourceLower (sourceIndex ⟨18,by decide⟩)) (sourceUpper (sourceIndex ⟨18,by decide⟩)) := by
  refine ⟨valid18,num28W,num28C,?_,?_⟩
  · intro θ hθ
    exact (geometry28W (fullCell28 hθ)).1
  · intro θ hθ
    exact (geometry28C (fullCell28 hθ)).1


theorem radius28 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨18,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨18,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨18,by decide⟩).cRadius :=
  ⟨(geometry28W (fullCell28 hθ)).2,(geometry28C (fullCell28 hθ)).2⟩


theorem fullCell29 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨19,by decide⟩)) :
    B (29687022568931659513550281 / 60000000000000000000000000) (991966295480402052191389 / 2000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 29 ≤ θ at hl
  change θ ≤ noiseNode 30 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply29 : Supply (parameters ⟨19,by decide⟩)
    (sourceLower (sourceIndex ⟨19,by decide⟩)) (sourceUpper (sourceIndex ⟨19,by decide⟩)) := by
  refine ⟨valid19,num29W,num29C,?_,?_⟩
  · intro θ hθ
    exact (geometry29W (fullCell29 hθ)).1
  · intro θ hθ
    exact (geometry29C (fullCell29 hθ)).1


theorem radius29 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨19,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨19,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨19,by decide⟩).cRadius :=
  ⟨(geometry29W (fullCell29 hθ)).2,(geometry29C (fullCell29 hθ)).2⟩


theorem fullCell30 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨20,by decide⟩)) :
    B (991966295480402052191389 / 2000000000000000000000000) (29830955159892463617933059 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 30 ≤ θ at hl
  change θ ≤ noiseNode 31 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply30 : Supply (parameters ⟨20,by decide⟩)
    (sourceLower (sourceIndex ⟨20,by decide⟩)) (sourceUpper (sourceIndex ⟨20,by decide⟩)) := by
  refine ⟨valid20,num30W,num30C,?_,?_⟩
  · intro θ hθ
    exact (geometry30W (fullCell30 hθ)).1
  · intro θ hθ
    exact (geometry30C (fullCell30 hθ)).1


theorem radius30 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨20,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨20,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨20,by decide⟩).cRadius :=
  ⟨(geometry30W (fullCell30 hθ)).2,(geometry30C (fullCell30 hθ)).2⟩


theorem fullCell31 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨21,by decide⟩)) :
    B (29830955159892463617933059 / 60000000000000000000000000) (934466295480402052191389 / 1875000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 31 ≤ θ at hl
  change θ ≤ noiseNode 32 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply31 : Supply (parameters ⟨21,by decide⟩)
    (sourceLower (sourceIndex ⟨21,by decide⟩)) (sourceUpper (sourceIndex ⟨21,by decide⟩)) := by
  refine ⟨valid21,num31W,num31C,?_,?_⟩
  · intro θ hθ
    exact (geometry31W (fullCell31 hθ)).1
  · intro θ hθ
    exact (geometry31C (fullCell31 hθ)).1


theorem radius31 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨21,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨21,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨21,by decide⟩).cRadius :=
  ⟨(geometry31W (fullCell31 hθ)).2,(geometry31C (fullCell31 hθ)).2⟩


theorem fullCell32 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨22,by decide⟩)) :
    B (934466295480402052191389 / 1875000000000000000000000) (9991629250284422574105279 / 20000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 32 ≤ θ at hl
  change θ ≤ noiseNode 33 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply32 : Supply (parameters ⟨22,by decide⟩)
    (sourceLower (sourceIndex ⟨22,by decide⟩)) (sourceUpper (sourceIndex ⟨22,by decide⟩)) := by
  refine ⟨valid22,num32W,num32C,?_,?_⟩
  · intro θ hθ
    exact (geometry32W (fullCell32 hθ)).1
  · intro θ hθ
    exact (geometry32C (fullCell32 hθ)).1


theorem radius32 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨22,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨22,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨22,by decide⟩).cRadius :=
  ⟨(geometry32W (fullCell32 hθ)).2,(geometry32C (fullCell32 hθ)).2⟩


theorem fullCell33 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨23,by decide⟩)) :
    B (9991629250284422574105279 / 20000000000000000000000000) (15023427023166834887253613 / 30000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 33 ≤ θ at hl
  change θ ≤ noiseNode 34 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply33 : Supply (parameters ⟨23,by decide⟩)
    (sourceLower (sourceIndex ⟨23,by decide⟩)) (sourceUpper (sourceIndex ⟨23,by decide⟩)) := by
  refine ⟨valid23,num33W,num33C,?_,?_⟩
  · intro θ hθ
    exact (geometry33W (fullCell33 hθ)).1
  · intro θ hθ
    exact (geometry33C (fullCell33 hθ)).1


theorem radius33 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨23,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨23,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨23,by decide⟩).cRadius :=
  ⟨(geometry33W (fullCell33 hθ)).2,(geometry33C (fullCell33 hθ)).2⟩


theorem fullCell34 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨24,by decide⟩)) :
    B (15023427023166834887253613 / 30000000000000000000000000) (6023764068362814365339723 / 12000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 34 ≤ θ at hl
  change θ ≤ noiseNode 35 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply34 : Supply (parameters ⟨24,by decide⟩)
    (sourceLower (sourceIndex ⟨24,by decide⟩)) (sourceUpper (sourceIndex ⟨24,by decide⟩)) := by
  refine ⟨valid24,num34W,num34C,?_,?_⟩
  · intro θ hθ
    exact (geometry34W (fullCell34 hθ)).1
  · intro θ hθ
    exact (geometry34C (fullCell34 hθ)).1


theorem radius34 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨24,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨24,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨24,by decide⟩).cRadius :=
  ⟨(geometry34W (fullCell34 hθ)).2,(geometry34C (fullCell34 hθ)).2⟩


theorem fullCell35 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨25,by decide⟩)) :
    B (6023764068362814365339723 / 12000000000000000000000000) (2515898886441206156574167 / 5000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 35 ≤ θ at hl
  change θ ≤ noiseNode 36 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply35 : Supply (parameters ⟨25,by decide⟩)
    (sourceLower (sourceIndex ⟨25,by decide⟩)) (sourceUpper (sourceIndex ⟨25,by decide⟩)) := by
  refine ⟨valid25,num35W,num35C,?_,?_⟩
  · intro θ hθ
    exact (geometry35W (fullCell35 hθ)).1
  · intro θ hθ
    exact (geometry35C (fullCell35 hθ)).1


theorem radius35 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨25,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨25,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨25,by decide⟩).cRadius :=
  ⟨(geometry35W (fullCell35 hθ)).2,(geometry35C (fullCell35 hθ)).2⟩


theorem fullCell36 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨26,by decide⟩)) :
    B (2515898886441206156574167 / 5000000000000000000000000) (30262752932774875931081393 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 36 ≤ θ at hl
  change θ ≤ noiseNode 37 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply36 : Supply (parameters ⟨26,by decide⟩)
    (sourceLower (sourceIndex ⟨26,by decide⟩)) (sourceUpper (sourceIndex ⟨26,by decide⟩)) := by
  refine ⟨valid26,num36W,num36C,?_,?_⟩
  · intro θ hθ
    exact (geometry36W (fullCell36 hθ)).1
  · intro θ hθ
    exact (geometry36C (fullCell36 hθ)).1


theorem radius36 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨26,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨26,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨26,by decide⟩).cRadius :=
  ⟨(geometry36W (fullCell36 hθ)).2,(geometry36C (fullCell36 hθ)).2⟩


theorem fullCell37 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨27,by decide⟩)) :
    B (30262752932774875931081393 / 60000000000000000000000000) (15167359614127638991636391 / 30000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 37 ≤ θ at hl
  change θ ≤ noiseNode 38 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply37 : Supply (parameters ⟨27,by decide⟩)
    (sourceLower (sourceIndex ⟨27,by decide⟩)) (sourceUpper (sourceIndex ⟨27,by decide⟩)) := by
  refine ⟨valid27,num37W,num37C,?_,?_⟩
  · intro θ hθ
    exact (geometry37W (fullCell37 hθ)).1
  · intro θ hθ
    exact (geometry37C (fullCell37 hθ)).1


theorem radius37 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨27,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨27,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨27,by decide⟩).cRadius :=
  ⟨(geometry37W (fullCell37 hθ)).2,(geometry37C (fullCell37 hθ)).2⟩


theorem fullCell38 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨28,by decide⟩)) :
    B (15167359614127638991636391 / 30000000000000000000000000) (10135561841245226678488057 / 20000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 38 ≤ θ at hl
  change θ ≤ noiseNode 39 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply38 : Supply (parameters ⟨28,by decide⟩)
    (sourceLower (sourceIndex ⟨28,by decide⟩)) (sourceUpper (sourceIndex ⟨28,by decide⟩)) := by
  refine ⟨valid28,num38W,num38C,?_,?_⟩
  · intro θ hθ
    exact (geometry38W (fullCell38 hθ)).1
  · intro θ hθ
    exact (geometry38C (fullCell38 hθ)).1


theorem radius38 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨28,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨28,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨28,by decide⟩).cRadius :=
  ⟨(geometry38W (fullCell38 hθ)).2,(geometry38C (fullCell38 hθ)).2⟩


theorem fullCell39 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨29,by decide⟩)) :
    B (10135561841245226678488057 / 20000000000000000000000000) (761966295480402052191389 / 1500000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 39 ≤ θ at hl
  change θ ≤ noiseNode 40 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply39 : Supply (parameters ⟨29,by decide⟩)
    (sourceLower (sourceIndex ⟨29,by decide⟩)) (sourceUpper (sourceIndex ⟨29,by decide⟩)) := by
  refine ⟨valid29,num39W,num39C,?_,?_⟩
  · intro θ hθ
    exact (geometry39W (fullCell39 hθ)).1
  · intro θ hθ
    exact (geometry39C (fullCell39 hθ)).1


theorem radius39 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨29,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨29,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨29,by decide⟩).cRadius :=
  ⟨(geometry39W (fullCell39 hθ)).2,(geometry39C (fullCell39 hθ)).2⟩


theorem fullCell40 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨30,by decide⟩)) :
    B (761966295480402052191389 / 1500000000000000000000000) (30550618114696484139846949 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 40 ≤ θ at hl
  change θ ≤ noiseNode 41 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply40 : Supply (parameters ⟨30,by decide⟩)
    (sourceLower (sourceIndex ⟨30,by decide⟩)) (sourceUpper (sourceIndex ⟨30,by decide⟩)) := by
  refine ⟨valid30,num40W,num40C,?_,?_⟩
  · intro θ hθ
    exact (geometry40W (fullCell40 hθ)).1
  · intro θ hθ
    exact (geometry40C (fullCell40 hθ)).1


theorem radius40 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨30,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨30,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨30,by decide⟩).cRadius :=
  ⟨(geometry40W (fullCell40 hθ)).2,(geometry40C (fullCell40 hθ)).2⟩


theorem fullCell41 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨31,by decide⟩)) :
    B (30550618114696484139846949 / 60000000000000000000000000) (5103764068362814365339723 / 10000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 41 ≤ θ at hl
  change θ ≤ noiseNode 42 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply41 : Supply (parameters ⟨31,by decide⟩)
    (sourceLower (sourceIndex ⟨31,by decide⟩)) (sourceUpper (sourceIndex ⟨31,by decide⟩)) := by
  refine ⟨valid31,num41W,num41C,?_,?_⟩
  · intro θ hθ
    exact (geometry41W (fullCell41 hθ)).1
  · intro θ hθ
    exact (geometry41C (fullCell41 hθ)).1


theorem radius41 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨31,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨31,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨31,by decide⟩).cRadius :=
  ⟨(geometry41W (fullCell41 hθ)).2,(geometry41C (fullCell41 hθ)).2⟩


theorem fullCell42 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨32,by decide⟩)) :
    B (5103764068362814365339723 / 10000000000000000000000000) (30694550705657288244229727 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 42 ≤ θ at hl
  change θ ≤ noiseNode 43 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply42 : Supply (parameters ⟨32,by decide⟩)
    (sourceLower (sourceIndex ⟨32,by decide⟩)) (sourceUpper (sourceIndex ⟨32,by decide⟩)) := by
  refine ⟨valid32,num42W,num42C,?_,?_⟩
  · intro θ hθ
    exact (geometry42W (fullCell42 hθ)).1
  · intro θ hθ
    exact (geometry42C (fullCell42 hθ)).1


theorem radius42 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨32,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨32,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨32,by decide⟩).cRadius :=
  ⟨(geometry42W (fullCell42 hθ)).2,(geometry42C (fullCell42 hθ)).2⟩


theorem fullCell43 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨33,by decide⟩)) :
    B (30694550705657288244229727 / 60000000000000000000000000) (7691629250284422574105279 / 15000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 43 ≤ θ at hl
  change θ ≤ noiseNode 44 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply43 : Supply (parameters ⟨33,by decide⟩)
    (sourceLower (sourceIndex ⟨33,by decide⟩)) (sourceUpper (sourceIndex ⟨33,by decide⟩)) := by
  refine ⟨valid33,num43W,num43C,?_,?_⟩
  · intro θ hθ
    exact (geometry43W (fullCell43 hθ)).1
  · intro θ hθ
    exact (geometry43C (fullCell43 hθ)).1


theorem radius43 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨33,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨33,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨33,by decide⟩).cRadius :=
  ⟨(geometry43W (fullCell43 hθ)).2,(geometry43C (fullCell43 hθ)).2⟩


theorem fullCell44 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨34,by decide⟩)) :
    B (7691629250284422574105279 / 15000000000000000000000000) (2055898886441206156574167 / 4000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 44 ≤ θ at hl
  change θ ≤ noiseNode 45 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply44 : Supply (parameters ⟨34,by decide⟩)
    (sourceLower (sourceIndex ⟨34,by decide⟩)) (sourceUpper (sourceIndex ⟨34,by decide⟩)) := by
  refine ⟨valid34,num44W,num44C,?_,?_⟩
  · intro θ hθ
    exact (geometry44W (fullCell44 hθ)).1
  · intro θ hθ
    exact (geometry44C (fullCell44 hθ)).1


theorem radius44 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨34,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨34,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨34,by decide⟩).cRadius :=
  ⟨(geometry44W (fullCell44 hθ)).2,(geometry44C (fullCell44 hθ)).2⟩


theorem fullCell45 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨35,by decide⟩)) :
    B (2055898886441206156574167 / 4000000000000000000000000) (15455224796049247200401947 / 30000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 45 ≤ θ at hl
  change θ ≤ noiseNode 46 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply45 : Supply (parameters ⟨35,by decide⟩)
    (sourceLower (sourceIndex ⟨35,by decide⟩)) (sourceUpper (sourceIndex ⟨35,by decide⟩)) := by
  refine ⟨valid35,num45W,num45C,?_,?_⟩
  · intro θ hθ
    exact (geometry45W (fullCell45 hθ)).1
  · intro θ hθ
    exact (geometry45C (fullCell45 hθ)).1


theorem radius45 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨35,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨35,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨35,by decide⟩).cRadius :=
  ⟨(geometry45W (fullCell45 hθ)).2,(geometry45C (fullCell45 hθ)).2⟩


theorem fullCell46 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨36,by decide⟩)) :
    B (15455224796049247200401947 / 30000000000000000000000000) (30982415887578896452995283 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 46 ≤ θ at hl
  change θ ≤ noiseNode 47 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply46 : Supply (parameters ⟨36,by decide⟩)
    (sourceLower (sourceIndex ⟨36,by decide⟩)) (sourceUpper (sourceIndex ⟨36,by decide⟩)) := by
  refine ⟨valid36,num46W,num46C,?_,?_⟩
  · intro θ hθ
    exact (geometry46W (fullCell46 hθ)).1
  · intro θ hθ
    exact (geometry46C (fullCell46 hθ)).1


theorem radius46 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨36,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨36,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨36,by decide⟩).cRadius :=
  ⟨(geometry46W (fullCell46 hθ)).2,(geometry46C (fullCell46 hθ)).2⟩


theorem fullCell47 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨37,by decide⟩)) :
    B (30982415887578896452995283 / 60000000000000000000000000) (646966295480402052191389 / 1250000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 47 ≤ θ at hl
  change θ ≤ noiseNode 48 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply47 : Supply (parameters ⟨37,by decide⟩)
    (sourceLower (sourceIndex ⟨37,by decide⟩)) (sourceUpper (sourceIndex ⟨37,by decide⟩)) := by
  refine ⟨valid37,num47W,num47C,?_,?_⟩
  · intro θ hθ
    exact (geometry47W (fullCell47 hθ)).1
  · intro θ hθ
    exact (geometry47C (fullCell47 hθ)).1


theorem radius47 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨37,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨37,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨37,by decide⟩).cRadius :=
  ⟨(geometry47W (fullCell47 hθ)).2,(geometry47C (fullCell47 hθ)).2⟩


theorem fullCell48 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨38,by decide⟩)) :
    B (646966295480402052191389 / 1250000000000000000000000) (31126348478539700557378061 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 48 ≤ θ at hl
  change θ ≤ noiseNode 49 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply48 : Supply (parameters ⟨38,by decide⟩)
    (sourceLower (sourceIndex ⟨38,by decide⟩)) (sourceUpper (sourceIndex ⟨38,by decide⟩)) := by
  refine ⟨valid38,num48W,num48C,?_,?_⟩
  · intro θ hθ
    exact (geometry48W (fullCell48 hθ)).1
  · intro θ hθ
    exact (geometry48C (fullCell48 hθ)).1


theorem radius48 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨38,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨38,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨38,by decide⟩).cRadius :=
  ⟨(geometry48W (fullCell48 hθ)).2,(geometry48C (fullCell48 hθ)).2⟩


theorem fullCell49 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨39,by decide⟩)) :
    B (31126348478539700557378061 / 60000000000000000000000000) (623966295480402052191389 / 1200000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 49 ≤ θ at hl
  change θ ≤ noiseNode 50 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply49 : Supply (parameters ⟨39,by decide⟩)
    (sourceLower (sourceIndex ⟨39,by decide⟩)) (sourceUpper (sourceIndex ⟨39,by decide⟩)) := by
  refine ⟨valid39,num49W,num49C,?_,?_⟩
  · intro θ hθ
    exact (geometry49W (fullCell49 hθ)).1
  · intro θ hθ
    exact (geometry49C (fullCell49 hθ)).1


theorem radius49 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨39,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨39,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨39,by decide⟩).cRadius :=
  ⟨(geometry49W (fullCell49 hθ)).2,(geometry49C (fullCell49 hθ)).2⟩


theorem fullCell50 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨40,by decide⟩)) :
    B (623966295480402052191389 / 1200000000000000000000000) (10423427023166834887253613 / 20000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 50 ≤ θ at hl
  change θ ≤ noiseNode 51 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply50 : Supply (parameters ⟨40,by decide⟩)
    (sourceLower (sourceIndex ⟨40,by decide⟩)) (sourceUpper (sourceIndex ⟨40,by decide⟩)) := by
  refine ⟨valid40,num50W,num50C,?_,?_⟩
  · intro θ hθ
    exact (geometry50W (fullCell50 hθ)).1
  · intro θ hθ
    exact (geometry50C (fullCell50 hθ)).1


theorem radius50 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨40,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨40,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨40,by decide⟩).cRadius :=
  ⟨(geometry50W (fullCell50 hθ)).2,(geometry50C (fullCell50 hθ)).2⟩


theorem fullCell51 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨41,by decide⟩)) :
    B (10423427023166834887253613 / 20000000000000000000000000) (7835561841245226678488057 / 15000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 51 ≤ θ at hl
  change θ ≤ noiseNode 52 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply51 : Supply (parameters ⟨41,by decide⟩)
    (sourceLower (sourceIndex ⟨41,by decide⟩)) (sourceUpper (sourceIndex ⟨41,by decide⟩)) := by
  refine ⟨valid41,num51W,num51C,?_,?_⟩
  · intro θ hθ
    exact (geometry51W (fullCell51 hθ)).1
  · intro θ hθ
    exact (geometry51C (fullCell51 hθ)).1


theorem radius51 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨41,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨41,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨41,by decide⟩).cRadius :=
  ⟨(geometry51W (fullCell51 hθ)).2,(geometry51C (fullCell51 hθ)).2⟩


theorem fullCell52 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨42,by decide⟩)) :
    B (7835561841245226678488057 / 15000000000000000000000000) (31414213660461308766143617 / 60000000000000000000000000) θ := by
  have hl := hθ.1
  have hu := hθ.2
  change noiseNode 52 ≤ θ at hl
  change θ ≤ noiseNode 53 at hu
  norm_num [noiseNode,proposedThetaUpper] at hl hu
  exact ⟨hl,hu⟩


theorem supply52 : Supply (parameters ⟨42,by decide⟩)
    (sourceLower (sourceIndex ⟨42,by decide⟩)) (sourceUpper (sourceIndex ⟨42,by decide⟩)) := by
  refine ⟨valid42,num52W,num52C,?_,?_⟩
  · intro θ hθ
    exact (geometry52W (fullCell52 hθ)).1
  · intro θ hθ
    exact (geometry52C (fullCell52 hθ)).1


theorem radius52 {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex ⟨42,by decide⟩)) :
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleWide ≤
      (parameters ⟨42,by decide⟩).wRadius ∧
    BstLean.Part199.radiusMinus 12225 θ BstLean.Part199.exampleCore ≤
      (parameters ⟨42,by decide⟩).cRadius :=
  ⟨(geometry52W (fullCell52 hθ)).2,(geometry52C (fullCell52 hθ)).2⟩


theorem supplies (j : Fin 43) : Supply (parameters j)
    (sourceLower (sourceIndex j)) (sourceUpper (sourceIndex j)) := by
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


theorem radii (j : Fin 43) {θ : ℝ} (hθ : θ ∈ sourceCell (sourceIndex j)) :
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

end BstLean.Part258
