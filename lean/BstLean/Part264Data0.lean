import BstLean.Part264PilotRepair
import BstLean.Part264Repair
/-! Rational envelope and frame checks for each dimension. -/
namespace BstLean.Part264
open Real Set BstLean.Part255 BstLean.Part263
noncomputable def cap12225 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976367 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138178003 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276758283 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277159561 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277559849 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (55591829 / 200000000 : ℝ)
  | ⟨6,_⟩ => (13917849 / 50000000 : ℝ)
  | ⟨7,_⟩ => (69688577 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279150659 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279546037 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279940443 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280333399 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140362939 / 500000000 : ℝ)
  | ⟨13,_⟩ => (70279227 / 250000000 : ℝ)
  | ⟨14,_⟩ => (28150787 / 100000000 : ℝ)
  | ⟨15,_⟩ => (70474433 / 250000000 : ℝ)
  | ⟨16,_⟩ => (5645733 / 20000000 : ℝ)
  | ⟨17,_⟩ => (70668659 / 250000000 : ℝ)
  | ⟨18,_⟩ => (141530841 / 500000000 : ℝ)
  | ⟨19,_⟩ => (141723899 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283832987 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (142108629 / 500000000 : ℝ)
  | ⟨22,_⟩ => (71150151 / 250000000 : ℝ)
  | ⟨23,_⟩ => (284982539 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (14268203 / 50000000 : ℝ)
  | ⟨25,_⟩ => (285744219 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286123973 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286502327 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286879783 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287256343 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (71907877 / 250000000 : ℝ)
  | ⟨31,_⟩ => (18000393 / 62500000 : ℝ)
  | ⟨32,_⟩ => (144190093 / 500000000 : ℝ)
  | ⟨33,_⟩ => (144376347 / 500000000 : ℝ)
  | ⟨34,_⟩ => (11564973 / 40000000 : ℝ)
  | ⟨35,_⟩ => (72373771 / 250000000 : ℝ)
  | ⟨36,_⟩ => (57972993 / 200000000 : ℝ)
  | ⟨37,_⟩ => (145116993 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290602141 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290968923 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58266969 / 200000000 : ℝ)
  | ⟨41,_⟩ => (58339983 / 200000000 : ℝ)
  | ⟨42,_⟩ => (292064131 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12225Cell0 :
    0 ≤ cap12225 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨0,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12225 ⟨0,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨0,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell1 :
    0 ≤ cap12225 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨1,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12225 ⟨1,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨1,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell2 :
    0 ≤ cap12225 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨2,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12225 ⟨2,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨2,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell3 :
    0 ≤ cap12225 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨3,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12225 ⟨3,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨3,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell4 :
    0 ≤ cap12225 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨4,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12225 ⟨4,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨4,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell5 :
    0 ≤ cap12225 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨5,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12225 ⟨5,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨5,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell6 :
    0 ≤ cap12225 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨6,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12225 ⟨6,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨6,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell7 :
    0 ≤ cap12225 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨7,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12225 ⟨7,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨7,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell8 :
    0 ≤ cap12225 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨8,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12225 ⟨8,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨8,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell9 :
    0 ≤ cap12225 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨9,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12225 ⟨9,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨9,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell10 :
    0 ≤ cap12225 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨10,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12225 ⟨10,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨10,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell11 :
    0 ≤ cap12225 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨11,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12225 ⟨11,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨11,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell12 :
    0 ≤ cap12225 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨12,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12225 ⟨12,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨12,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell13 :
    0 ≤ cap12225 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨13,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12225 ⟨13,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨13,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell14 :
    0 ≤ cap12225 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨14,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12225 ⟨14,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨14,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell15 :
    0 ≤ cap12225 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨15,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12225 ⟨15,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨15,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell16 :
    0 ≤ cap12225 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨16,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12225 ⟨16,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨16,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell17 :
    0 ≤ cap12225 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨17,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12225 ⟨17,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨17,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell18 :
    0 ≤ cap12225 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨18,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12225 ⟨18,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨18,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell19 :
    0 ≤ cap12225 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨19,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12225 ⟨19,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨19,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell20 :
    0 ≤ cap12225 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨20,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12225 ⟨20,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨20,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell21 :
    0 ≤ cap12225 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨21,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12225 ⟨21,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨21,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell22 :
    0 ≤ cap12225 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨22,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12225 ⟨22,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨22,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell23 :
    0 ≤ cap12225 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨23,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12225 ⟨23,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨23,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell24 :
    0 ≤ cap12225 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨24,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12225 ⟨24,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨24,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell25 :
    0 ≤ cap12225 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨25,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12225 ⟨25,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨25,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell26 :
    0 ≤ cap12225 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨26,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12225 ⟨26,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨26,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell27 :
    0 ≤ cap12225 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨27,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12225 ⟨27,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨27,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell28 :
    0 ≤ cap12225 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨28,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12225 ⟨28,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨28,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell29 :
    0 ≤ cap12225 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨29,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12225 ⟨29,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨29,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell30 :
    0 ≤ cap12225 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨30,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12225 ⟨30,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨30,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell31 :
    0 ≤ cap12225 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨31,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12225 ⟨31,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨31,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell32 :
    0 ≤ cap12225 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨32,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12225 ⟨32,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨32,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell33 :
    0 ≤ cap12225 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨33,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12225 ⟨33,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨33,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell34 :
    0 ≤ cap12225 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨34,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12225 ⟨34,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨34,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell35 :
    0 ≤ cap12225 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨35,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12225 ⟨35,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨35,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell36 :
    0 ≤ cap12225 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨36,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12225 ⟨36,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨36,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell37 :
    0 ≤ cap12225 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨37,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12225 ⟨37,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨37,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell38 :
    0 ≤ cap12225 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨38,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12225 ⟨38,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨38,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell39 :
    0 ≤ cap12225 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨39,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12225 ⟨39,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨39,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell40 :
    0 ≤ cap12225 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨40,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12225 ⟨40,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨40,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell41 :
    0 ≤ cap12225 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨41,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12225 ⟨41,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨41,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cell42 :
    0 ≤ cap12225 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12225 (parameters ⟨42,by decide⟩)
      (scalarRow12225.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12225 ⟨42,by decide⟩ ∧
    (scalarRow12225.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 ⟨42,by decide⟩ + (scalarRow12225.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12225.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12225.targetFrame := by
  norm_num [cap12225, scalarRow12225, sourceIndex, cell12225, BstLean.Part263.envelope, parameters]

theorem repair12225Cells (j : Fin 43) :
    0 ≤ cap12225 j ∧
    BstLean.Part263.envelope 12225 (parameters j) (scalarRow12225.table (sourceIndex j)).upper ≤ cap12225 j ∧
    (scalarRow12225.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12225 j + (scalarRow12225.table (sourceIndex j)).centre) /
      (scalarRow12225.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12225.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12225Cell0
  | ⟨1,_⟩ => exact repair12225Cell1
  | ⟨2,_⟩ => exact repair12225Cell2
  | ⟨3,_⟩ => exact repair12225Cell3
  | ⟨4,_⟩ => exact repair12225Cell4
  | ⟨5,_⟩ => exact repair12225Cell5
  | ⟨6,_⟩ => exact repair12225Cell6
  | ⟨7,_⟩ => exact repair12225Cell7
  | ⟨8,_⟩ => exact repair12225Cell8
  | ⟨9,_⟩ => exact repair12225Cell9
  | ⟨10,_⟩ => exact repair12225Cell10
  | ⟨11,_⟩ => exact repair12225Cell11
  | ⟨12,_⟩ => exact repair12225Cell12
  | ⟨13,_⟩ => exact repair12225Cell13
  | ⟨14,_⟩ => exact repair12225Cell14
  | ⟨15,_⟩ => exact repair12225Cell15
  | ⟨16,_⟩ => exact repair12225Cell16
  | ⟨17,_⟩ => exact repair12225Cell17
  | ⟨18,_⟩ => exact repair12225Cell18
  | ⟨19,_⟩ => exact repair12225Cell19
  | ⟨20,_⟩ => exact repair12225Cell20
  | ⟨21,_⟩ => exact repair12225Cell21
  | ⟨22,_⟩ => exact repair12225Cell22
  | ⟨23,_⟩ => exact repair12225Cell23
  | ⟨24,_⟩ => exact repair12225Cell24
  | ⟨25,_⟩ => exact repair12225Cell25
  | ⟨26,_⟩ => exact repair12225Cell26
  | ⟨27,_⟩ => exact repair12225Cell27
  | ⟨28,_⟩ => exact repair12225Cell28
  | ⟨29,_⟩ => exact repair12225Cell29
  | ⟨30,_⟩ => exact repair12225Cell30
  | ⟨31,_⟩ => exact repair12225Cell31
  | ⟨32,_⟩ => exact repair12225Cell32
  | ⟨33,_⟩ => exact repair12225Cell33
  | ⟨34,_⟩ => exact repair12225Cell34
  | ⟨35,_⟩ => exact repair12225Cell35
  | ⟨36,_⟩ => exact repair12225Cell36
  | ⟨37,_⟩ => exact repair12225Cell37
  | ⟨38,_⟩ => exact repair12225Cell38
  | ⟨39,_⟩ => exact repair12225Cell39
  | ⟨40,_⟩ => exact repair12225Cell40
  | ⟨41,_⟩ => exact repair12225Cell41
  | ⟨42,_⟩ => exact repair12225Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12225 : FrameRepair 12225 scalarRow12225 where
  cap := cap12225
  cap_nonneg := fun j => (repair12225Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12225])
  endpoint := fun j => (repair12225Cells j).2.1
  endpoint_upper := fun j => (repair12225Cells j).2.2.1
  frame := fun j => (repair12225Cells j).2.2.2

noncomputable def cap12227 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976291 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276355841 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (55351621 / 200000000 : ℝ)
  | ⟨3,_⟩ => (27715937 / 100000000 : ℝ)
  | ⟨4,_⟩ => (55511929 / 200000000 : ℝ)
  | ⟨5,_⟩ => (17372433 / 62500000 : ℝ)
  | ⟨6,_⟩ => (1113427 / 4000000 : ℝ)
  | ⟨7,_⟩ => (55750813 / 200000000 : ℝ)
  | ⟨8,_⟩ => (279150403 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (34943221 / 125000000 : ℝ)
  | ⟨10,_⟩ => (279940161 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56066621 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280725571 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70279147 / 250000000 : ℝ)
  | ⟨14,_⟩ => (140753769 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281897387 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282286293 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141337133 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283061299 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283447403 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283832579 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284216837 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284600171 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284982093 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142681801 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285743749 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (28612349 / 100000000 : ℝ)
  | ⟨27,_⟩ => (35812729 / 125000000 : ℝ)
  | ⟨28,_⟩ => (71719819 / 250000000 : ℝ)
  | ⟨29,_⟩ => (287255823 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (2247117 / 7812500 : ℝ)
  | ⟨31,_⟩ => (18000359 / 62500000 : ℝ)
  | ⟨32,_⟩ => (28837963 / 100000000 : ℝ)
  | ⟨33,_⟩ => (2310017 / 8000000 : ℝ)
  | ⟨34,_⟩ => (9035117 / 31250000 : ℝ)
  | ⟨35,_⟩ => (289494491 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (7246609 / 25000000 : ℝ)
  | ⟨37,_⟩ => (290233369 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (36325189 / 125000000 : ℝ)
  | ⟨39,_⟩ => (290968281 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291334191 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291699249 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146031727 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12227Cell0 :
    0 ≤ cap12227 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨0,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12227 ⟨0,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨0,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell1 :
    0 ≤ cap12227 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨1,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12227 ⟨1,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨1,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell2 :
    0 ≤ cap12227 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨2,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12227 ⟨2,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨2,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell3 :
    0 ≤ cap12227 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨3,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12227 ⟨3,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨3,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell4 :
    0 ≤ cap12227 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨4,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12227 ⟨4,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨4,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell5 :
    0 ≤ cap12227 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨5,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12227 ⟨5,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨5,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell6 :
    0 ≤ cap12227 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨6,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12227 ⟨6,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨6,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell7 :
    0 ≤ cap12227 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨7,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12227 ⟨7,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨7,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell8 :
    0 ≤ cap12227 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨8,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12227 ⟨8,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨8,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell9 :
    0 ≤ cap12227 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨9,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12227 ⟨9,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨9,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell10 :
    0 ≤ cap12227 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨10,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12227 ⟨10,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨10,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell11 :
    0 ≤ cap12227 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨11,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12227 ⟨11,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨11,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell12 :
    0 ≤ cap12227 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨12,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12227 ⟨12,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨12,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell13 :
    0 ≤ cap12227 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨13,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12227 ⟨13,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨13,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell14 :
    0 ≤ cap12227 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨14,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12227 ⟨14,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨14,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell15 :
    0 ≤ cap12227 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨15,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12227 ⟨15,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨15,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell16 :
    0 ≤ cap12227 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨16,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12227 ⟨16,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨16,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell17 :
    0 ≤ cap12227 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨17,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12227 ⟨17,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨17,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell18 :
    0 ≤ cap12227 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨18,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12227 ⟨18,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨18,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell19 :
    0 ≤ cap12227 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨19,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12227 ⟨19,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨19,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell20 :
    0 ≤ cap12227 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨20,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12227 ⟨20,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨20,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell21 :
    0 ≤ cap12227 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨21,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12227 ⟨21,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨21,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell22 :
    0 ≤ cap12227 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨22,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12227 ⟨22,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨22,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell23 :
    0 ≤ cap12227 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨23,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12227 ⟨23,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨23,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell24 :
    0 ≤ cap12227 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨24,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12227 ⟨24,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨24,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell25 :
    0 ≤ cap12227 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨25,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12227 ⟨25,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨25,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell26 :
    0 ≤ cap12227 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨26,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12227 ⟨26,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨26,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell27 :
    0 ≤ cap12227 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨27,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12227 ⟨27,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨27,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell28 :
    0 ≤ cap12227 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨28,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12227 ⟨28,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨28,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell29 :
    0 ≤ cap12227 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨29,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12227 ⟨29,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨29,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell30 :
    0 ≤ cap12227 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨30,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12227 ⟨30,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨30,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell31 :
    0 ≤ cap12227 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨31,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12227 ⟨31,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨31,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell32 :
    0 ≤ cap12227 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨32,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12227 ⟨32,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨32,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell33 :
    0 ≤ cap12227 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨33,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12227 ⟨33,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨33,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell34 :
    0 ≤ cap12227 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨34,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12227 ⟨34,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨34,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell35 :
    0 ≤ cap12227 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨35,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12227 ⟨35,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨35,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell36 :
    0 ≤ cap12227 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨36,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12227 ⟨36,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨36,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell37 :
    0 ≤ cap12227 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨37,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12227 ⟨37,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨37,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell38 :
    0 ≤ cap12227 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨38,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12227 ⟨38,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨38,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell39 :
    0 ≤ cap12227 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨39,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12227 ⟨39,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨39,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell40 :
    0 ≤ cap12227 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨40,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12227 ⟨40,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨40,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell41 :
    0 ≤ cap12227 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨41,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12227 ⟨41,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨41,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cell42 :
    0 ≤ cap12227 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12227 (parameters ⟨42,by decide⟩)
      (scalarRow12227.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12227 ⟨42,by decide⟩ ∧
    (scalarRow12227.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 ⟨42,by decide⟩ + (scalarRow12227.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12227.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12227.targetFrame := by
  norm_num [cap12227, scalarRow12227, sourceIndex, cell12227, BstLean.Part263.envelope, parameters]

theorem repair12227Cells (j : Fin 43) :
    0 ≤ cap12227 j ∧
    BstLean.Part263.envelope 12227 (parameters j) (scalarRow12227.table (sourceIndex j)).upper ≤ cap12227 j ∧
    (scalarRow12227.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12227 j + (scalarRow12227.table (sourceIndex j)).centre) /
      (scalarRow12227.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12227.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12227Cell0
  | ⟨1,_⟩ => exact repair12227Cell1
  | ⟨2,_⟩ => exact repair12227Cell2
  | ⟨3,_⟩ => exact repair12227Cell3
  | ⟨4,_⟩ => exact repair12227Cell4
  | ⟨5,_⟩ => exact repair12227Cell5
  | ⟨6,_⟩ => exact repair12227Cell6
  | ⟨7,_⟩ => exact repair12227Cell7
  | ⟨8,_⟩ => exact repair12227Cell8
  | ⟨9,_⟩ => exact repair12227Cell9
  | ⟨10,_⟩ => exact repair12227Cell10
  | ⟨11,_⟩ => exact repair12227Cell11
  | ⟨12,_⟩ => exact repair12227Cell12
  | ⟨13,_⟩ => exact repair12227Cell13
  | ⟨14,_⟩ => exact repair12227Cell14
  | ⟨15,_⟩ => exact repair12227Cell15
  | ⟨16,_⟩ => exact repair12227Cell16
  | ⟨17,_⟩ => exact repair12227Cell17
  | ⟨18,_⟩ => exact repair12227Cell18
  | ⟨19,_⟩ => exact repair12227Cell19
  | ⟨20,_⟩ => exact repair12227Cell20
  | ⟨21,_⟩ => exact repair12227Cell21
  | ⟨22,_⟩ => exact repair12227Cell22
  | ⟨23,_⟩ => exact repair12227Cell23
  | ⟨24,_⟩ => exact repair12227Cell24
  | ⟨25,_⟩ => exact repair12227Cell25
  | ⟨26,_⟩ => exact repair12227Cell26
  | ⟨27,_⟩ => exact repair12227Cell27
  | ⟨28,_⟩ => exact repair12227Cell28
  | ⟨29,_⟩ => exact repair12227Cell29
  | ⟨30,_⟩ => exact repair12227Cell30
  | ⟨31,_⟩ => exact repair12227Cell31
  | ⟨32,_⟩ => exact repair12227Cell32
  | ⟨33,_⟩ => exact repair12227Cell33
  | ⟨34,_⟩ => exact repair12227Cell34
  | ⟨35,_⟩ => exact repair12227Cell35
  | ⟨36,_⟩ => exact repair12227Cell36
  | ⟨37,_⟩ => exact repair12227Cell37
  | ⟨38,_⟩ => exact repair12227Cell38
  | ⟨39,_⟩ => exact repair12227Cell39
  | ⟨40,_⟩ => exact repair12227Cell40
  | ⟨41,_⟩ => exact repair12227Cell41
  | ⟨42,_⟩ => exact repair12227Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12227 : FrameRepair 12227 scalarRow12227 where
  cap := cap12227
  cap_nonneg := fun j => (repair12227Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12227])
  endpoint := fun j => (repair12227Cells j).2.1
  endpoint_upper := fun j => (repair12227Cells j).2.2.1
  frame := fun j => (repair12227Cells j).2.2.2

noncomputable def cap12228 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976253 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138177879 / 500000000 : ℝ)
  | ⟨2,_⟩ => (540543 / 1953125 : ℝ)
  | ⟨3,_⟩ => (11086371 / 40000000 : ℝ)
  | ⟨4,_⟩ => (138779771 / 500000000 : ℝ)
  | ⟨5,_⟩ => (13897941 / 50000000 : ℝ)
  | ⟨6,_⟩ => (55671327 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278753943 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (11166011 / 40000000 : ℝ)
  | ⟨9,_⟩ => (139772817 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279940021 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140166479 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280725417 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281116429 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (70376843 / 250000000 : ℝ)
  | ⟨15,_⟩ => (56379443 / 200000000 : ℝ)
  | ⟨16,_⟩ => (141143057 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282674081 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (70765277 / 250000000 : ℝ)
  | ⟨19,_⟩ => (56689441 / 200000000 : ℝ)
  | ⟨20,_⟩ => (2270659 / 8000000 : ℝ)
  | ⟨21,_⟩ => (284216627 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (56919991 / 200000000 : ℝ)
  | ⟨23,_⟩ => (284981871 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285363373 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142871757 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286123249 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (17906349 / 62500000 : ℝ)
  | ⟨28,_⟩ => (143439511 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287255563 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (28763071 / 100000000 : ℝ)
  | ⟨31,_⟩ => (9000171 / 31250000 : ℝ)
  | ⟨32,_⟩ => (36047419 / 125000000 : ℝ)
  | ⟨33,_⟩ => (288751841 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144561727 / 500000000 : ℝ)
  | ⟨35,_⟩ => (144747097 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289864057 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (14511653 / 50000000 : ℝ)
  | ⟨38,_⟩ => (290601197 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290967961 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58266773 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291698917 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (73015779 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12228Cell0 :
    0 ≤ cap12228 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨0,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12228 ⟨0,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨0,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell1 :
    0 ≤ cap12228 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨1,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12228 ⟨1,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨1,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell2 :
    0 ≤ cap12228 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨2,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12228 ⟨2,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨2,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell3 :
    0 ≤ cap12228 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨3,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12228 ⟨3,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨3,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell4 :
    0 ≤ cap12228 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨4,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12228 ⟨4,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨4,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell5 :
    0 ≤ cap12228 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨5,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12228 ⟨5,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨5,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell6 :
    0 ≤ cap12228 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨6,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12228 ⟨6,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨6,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell7 :
    0 ≤ cap12228 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨7,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12228 ⟨7,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨7,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell8 :
    0 ≤ cap12228 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨8,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12228 ⟨8,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨8,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell9 :
    0 ≤ cap12228 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨9,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12228 ⟨9,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨9,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell10 :
    0 ≤ cap12228 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨10,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12228 ⟨10,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨10,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell11 :
    0 ≤ cap12228 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨11,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12228 ⟨11,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨11,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell12 :
    0 ≤ cap12228 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨12,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12228 ⟨12,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨12,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell13 :
    0 ≤ cap12228 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨13,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12228 ⟨13,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨13,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell14 :
    0 ≤ cap12228 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨14,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12228 ⟨14,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨14,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell15 :
    0 ≤ cap12228 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨15,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12228 ⟨15,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨15,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell16 :
    0 ≤ cap12228 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨16,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12228 ⟨16,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨16,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell17 :
    0 ≤ cap12228 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨17,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12228 ⟨17,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨17,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell18 :
    0 ≤ cap12228 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨18,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12228 ⟨18,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨18,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell19 :
    0 ≤ cap12228 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨19,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12228 ⟨19,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨19,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell20 :
    0 ≤ cap12228 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨20,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12228 ⟨20,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨20,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell21 :
    0 ≤ cap12228 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨21,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12228 ⟨21,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨21,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell22 :
    0 ≤ cap12228 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨22,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12228 ⟨22,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨22,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell23 :
    0 ≤ cap12228 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨23,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12228 ⟨23,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨23,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell24 :
    0 ≤ cap12228 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨24,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12228 ⟨24,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨24,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell25 :
    0 ≤ cap12228 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨25,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12228 ⟨25,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨25,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell26 :
    0 ≤ cap12228 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨26,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12228 ⟨26,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨26,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell27 :
    0 ≤ cap12228 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨27,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12228 ⟨27,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨27,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell28 :
    0 ≤ cap12228 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨28,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12228 ⟨28,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨28,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell29 :
    0 ≤ cap12228 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨29,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12228 ⟨29,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨29,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell30 :
    0 ≤ cap12228 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨30,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12228 ⟨30,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨30,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell31 :
    0 ≤ cap12228 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨31,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12228 ⟨31,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨31,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell32 :
    0 ≤ cap12228 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨32,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12228 ⟨32,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨32,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell33 :
    0 ≤ cap12228 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨33,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12228 ⟨33,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨33,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell34 :
    0 ≤ cap12228 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨34,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12228 ⟨34,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨34,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell35 :
    0 ≤ cap12228 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨35,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12228 ⟨35,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨35,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell36 :
    0 ≤ cap12228 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨36,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12228 ⟨36,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨36,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell37 :
    0 ≤ cap12228 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨37,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12228 ⟨37,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨37,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell38 :
    0 ≤ cap12228 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨38,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12228 ⟨38,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨38,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell39 :
    0 ≤ cap12228 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨39,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12228 ⟨39,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨39,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell40 :
    0 ≤ cap12228 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨40,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12228 ⟨40,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨40,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell41 :
    0 ≤ cap12228 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨41,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12228 ⟨41,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨41,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cell42 :
    0 ≤ cap12228 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12228 (parameters ⟨42,by decide⟩)
      (scalarRow12228.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12228 ⟨42,by decide⟩ ∧
    (scalarRow12228.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 ⟨42,by decide⟩ + (scalarRow12228.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12228.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12228.targetFrame := by
  norm_num [cap12228, scalarRow12228, sourceIndex, cell12228, BstLean.Part263.envelope, parameters]

theorem repair12228Cells (j : Fin 43) :
    0 ≤ cap12228 j ∧
    BstLean.Part263.envelope 12228 (parameters j) (scalarRow12228.table (sourceIndex j)).upper ≤ cap12228 j ∧
    (scalarRow12228.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12228 j + (scalarRow12228.table (sourceIndex j)).centre) /
      (scalarRow12228.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12228.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12228Cell0
  | ⟨1,_⟩ => exact repair12228Cell1
  | ⟨2,_⟩ => exact repair12228Cell2
  | ⟨3,_⟩ => exact repair12228Cell3
  | ⟨4,_⟩ => exact repair12228Cell4
  | ⟨5,_⟩ => exact repair12228Cell5
  | ⟨6,_⟩ => exact repair12228Cell6
  | ⟨7,_⟩ => exact repair12228Cell7
  | ⟨8,_⟩ => exact repair12228Cell8
  | ⟨9,_⟩ => exact repair12228Cell9
  | ⟨10,_⟩ => exact repair12228Cell10
  | ⟨11,_⟩ => exact repair12228Cell11
  | ⟨12,_⟩ => exact repair12228Cell12
  | ⟨13,_⟩ => exact repair12228Cell13
  | ⟨14,_⟩ => exact repair12228Cell14
  | ⟨15,_⟩ => exact repair12228Cell15
  | ⟨16,_⟩ => exact repair12228Cell16
  | ⟨17,_⟩ => exact repair12228Cell17
  | ⟨18,_⟩ => exact repair12228Cell18
  | ⟨19,_⟩ => exact repair12228Cell19
  | ⟨20,_⟩ => exact repair12228Cell20
  | ⟨21,_⟩ => exact repair12228Cell21
  | ⟨22,_⟩ => exact repair12228Cell22
  | ⟨23,_⟩ => exact repair12228Cell23
  | ⟨24,_⟩ => exact repair12228Cell24
  | ⟨25,_⟩ => exact repair12228Cell25
  | ⟨26,_⟩ => exact repair12228Cell26
  | ⟨27,_⟩ => exact repair12228Cell27
  | ⟨28,_⟩ => exact repair12228Cell28
  | ⟨29,_⟩ => exact repair12228Cell29
  | ⟨30,_⟩ => exact repair12228Cell30
  | ⟨31,_⟩ => exact repair12228Cell31
  | ⟨32,_⟩ => exact repair12228Cell32
  | ⟨33,_⟩ => exact repair12228Cell33
  | ⟨34,_⟩ => exact repair12228Cell34
  | ⟨35,_⟩ => exact repair12228Cell35
  | ⟨36,_⟩ => exact repair12228Cell36
  | ⟨37,_⟩ => exact repair12228Cell37
  | ⟨38,_⟩ => exact repair12228Cell38
  | ⟨39,_⟩ => exact repair12228Cell39
  | ⟨40,_⟩ => exact repair12228Cell40
  | ⟨41,_⟩ => exact repair12228Cell41
  | ⟨42,_⟩ => exact repair12228Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12228 : FrameRepair 12228 scalarRow12228 where
  cap := cap12228
  cap_nonneg := fun j => (repair12228Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12228])
  endpoint := fun j => (repair12228Cells j).2.1
  endpoint_upper := fun j => (repair12228Cells j).2.2.1
  frame := fun j => (repair12228Cells j).2.2.2

noncomputable def cap12229 : Fin 43 → ℝ
  | ⟨0,_⟩ => (27595243 / 100000000 : ℝ)
  | ⟨1,_⟩ => (69088919 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276757927 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277159179 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (3469493 / 12500000 : ℝ)
  | ⟨5,_⟩ => (277958711 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (6958913 / 25000000 : ℝ)
  | ⟨7,_⟩ => (139376911 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279150147 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279545499 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (6998497 / 25000000 : ℝ)
  | ⟨11,_⟩ => (280332811 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (17545329 / 62500000 : ℝ)
  | ⟨13,_⟩ => (281116269 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140753603 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140948521 / 500000000 : ℝ)
  | ⟨16,_⟩ => (56457187 / 200000000 : ℝ)
  | ⟨17,_⟩ => (35334237 / 125000000 : ℝ)
  | ⟨18,_⟩ => (70765229 / 250000000 : ℝ)
  | ⟨19,_⟩ => (8857719 / 31250000 : ℝ)
  | ⟨20,_⟩ => (283832171 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284216417 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142299869 / 500000000 : ℝ)
  | ⟨23,_⟩ => (17811353 / 62500000 : ℝ)
  | ⟨24,_⟩ => (35670393 / 125000000 : ℝ)
  | ⟨25,_⟩ => (285743279 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (558834 / 1953125 : ℝ)
  | ⟨27,_⟩ => (286501337 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (17929923 / 62500000 : ℝ)
  | ⟨29,_⟩ => (287255303 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (71907611 / 250000000 : ℝ)
  | ⟨31,_⟩ => (720013 / 2500000 : ℝ)
  | ⟨32,_⟩ => (144189537 / 500000000 : ℝ)
  | ⟨33,_⟩ => (72187889 / 250000000 : ℝ)
  | ⟨34,_⟩ => (289123163 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144746949 / 500000000 : ℝ)
  | ⟨36,_⟩ => (57972751 / 200000000 : ℝ)
  | ⟨37,_⟩ => (18139547 / 62500000 : ℝ)
  | ⟨38,_⟩ => (290600883 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (7274191 / 25000000 : ℝ)
  | ⟨40,_⟩ => (145666769 / 500000000 : ℝ)
  | ⟨41,_⟩ => (36462323 / 125000000 : ℝ)
  | ⟨42,_⟩ => (292062777 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12229Cell0 :
    0 ≤ cap12229 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨0,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12229 ⟨0,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨0,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell1 :
    0 ≤ cap12229 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨1,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12229 ⟨1,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨1,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell2 :
    0 ≤ cap12229 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨2,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12229 ⟨2,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨2,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell3 :
    0 ≤ cap12229 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨3,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12229 ⟨3,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨3,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell4 :
    0 ≤ cap12229 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨4,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12229 ⟨4,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨4,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell5 :
    0 ≤ cap12229 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨5,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12229 ⟨5,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨5,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell6 :
    0 ≤ cap12229 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨6,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12229 ⟨6,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨6,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell7 :
    0 ≤ cap12229 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨7,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12229 ⟨7,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨7,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell8 :
    0 ≤ cap12229 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨8,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12229 ⟨8,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨8,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell9 :
    0 ≤ cap12229 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨9,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12229 ⟨9,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨9,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell10 :
    0 ≤ cap12229 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨10,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12229 ⟨10,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨10,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell11 :
    0 ≤ cap12229 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨11,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12229 ⟨11,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨11,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell12 :
    0 ≤ cap12229 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨12,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12229 ⟨12,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨12,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell13 :
    0 ≤ cap12229 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨13,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12229 ⟨13,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨13,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell14 :
    0 ≤ cap12229 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨14,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12229 ⟨14,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨14,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell15 :
    0 ≤ cap12229 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨15,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12229 ⟨15,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨15,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell16 :
    0 ≤ cap12229 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨16,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12229 ⟨16,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨16,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell17 :
    0 ≤ cap12229 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨17,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12229 ⟨17,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨17,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell18 :
    0 ≤ cap12229 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨18,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12229 ⟨18,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨18,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell19 :
    0 ≤ cap12229 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨19,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12229 ⟨19,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨19,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell20 :
    0 ≤ cap12229 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨20,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12229 ⟨20,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨20,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell21 :
    0 ≤ cap12229 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨21,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12229 ⟨21,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨21,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell22 :
    0 ≤ cap12229 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨22,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12229 ⟨22,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨22,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell23 :
    0 ≤ cap12229 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨23,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12229 ⟨23,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨23,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell24 :
    0 ≤ cap12229 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨24,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12229 ⟨24,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨24,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell25 :
    0 ≤ cap12229 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨25,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12229 ⟨25,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨25,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell26 :
    0 ≤ cap12229 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨26,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12229 ⟨26,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨26,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell27 :
    0 ≤ cap12229 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨27,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12229 ⟨27,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨27,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell28 :
    0 ≤ cap12229 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨28,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12229 ⟨28,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨28,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell29 :
    0 ≤ cap12229 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨29,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12229 ⟨29,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨29,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell30 :
    0 ≤ cap12229 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨30,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12229 ⟨30,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨30,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell31 :
    0 ≤ cap12229 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨31,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12229 ⟨31,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨31,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell32 :
    0 ≤ cap12229 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨32,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12229 ⟨32,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨32,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell33 :
    0 ≤ cap12229 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨33,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12229 ⟨33,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨33,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell34 :
    0 ≤ cap12229 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨34,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12229 ⟨34,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨34,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell35 :
    0 ≤ cap12229 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨35,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12229 ⟨35,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨35,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell36 :
    0 ≤ cap12229 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨36,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12229 ⟨36,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨36,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell37 :
    0 ≤ cap12229 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨37,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12229 ⟨37,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨37,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell38 :
    0 ≤ cap12229 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨38,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12229 ⟨38,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨38,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell39 :
    0 ≤ cap12229 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨39,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12229 ⟨39,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨39,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell40 :
    0 ≤ cap12229 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨40,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12229 ⟨40,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨40,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell41 :
    0 ≤ cap12229 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨41,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12229 ⟨41,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨41,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cell42 :
    0 ≤ cap12229 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12229 (parameters ⟨42,by decide⟩)
      (scalarRow12229.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12229 ⟨42,by decide⟩ ∧
    (scalarRow12229.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 ⟨42,by decide⟩ + (scalarRow12229.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12229.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12229.targetFrame := by
  norm_num [cap12229, scalarRow12229, sourceIndex, cell12229, BstLean.Part263.envelope, parameters]

theorem repair12229Cells (j : Fin 43) :
    0 ≤ cap12229 j ∧
    BstLean.Part263.envelope 12229 (parameters j) (scalarRow12229.table (sourceIndex j)).upper ≤ cap12229 j ∧
    (scalarRow12229.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12229 j + (scalarRow12229.table (sourceIndex j)).centre) /
      (scalarRow12229.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12229.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12229Cell0
  | ⟨1,_⟩ => exact repair12229Cell1
  | ⟨2,_⟩ => exact repair12229Cell2
  | ⟨3,_⟩ => exact repair12229Cell3
  | ⟨4,_⟩ => exact repair12229Cell4
  | ⟨5,_⟩ => exact repair12229Cell5
  | ⟨6,_⟩ => exact repair12229Cell6
  | ⟨7,_⟩ => exact repair12229Cell7
  | ⟨8,_⟩ => exact repair12229Cell8
  | ⟨9,_⟩ => exact repair12229Cell9
  | ⟨10,_⟩ => exact repair12229Cell10
  | ⟨11,_⟩ => exact repair12229Cell11
  | ⟨12,_⟩ => exact repair12229Cell12
  | ⟨13,_⟩ => exact repair12229Cell13
  | ⟨14,_⟩ => exact repair12229Cell14
  | ⟨15,_⟩ => exact repair12229Cell15
  | ⟨16,_⟩ => exact repair12229Cell16
  | ⟨17,_⟩ => exact repair12229Cell17
  | ⟨18,_⟩ => exact repair12229Cell18
  | ⟨19,_⟩ => exact repair12229Cell19
  | ⟨20,_⟩ => exact repair12229Cell20
  | ⟨21,_⟩ => exact repair12229Cell21
  | ⟨22,_⟩ => exact repair12229Cell22
  | ⟨23,_⟩ => exact repair12229Cell23
  | ⟨24,_⟩ => exact repair12229Cell24
  | ⟨25,_⟩ => exact repair12229Cell25
  | ⟨26,_⟩ => exact repair12229Cell26
  | ⟨27,_⟩ => exact repair12229Cell27
  | ⟨28,_⟩ => exact repair12229Cell28
  | ⟨29,_⟩ => exact repair12229Cell29
  | ⟨30,_⟩ => exact repair12229Cell30
  | ⟨31,_⟩ => exact repair12229Cell31
  | ⟨32,_⟩ => exact repair12229Cell32
  | ⟨33,_⟩ => exact repair12229Cell33
  | ⟨34,_⟩ => exact repair12229Cell34
  | ⟨35,_⟩ => exact repair12229Cell35
  | ⟨36,_⟩ => exact repair12229Cell36
  | ⟨37,_⟩ => exact repair12229Cell37
  | ⟨38,_⟩ => exact repair12229Cell38
  | ⟨39,_⟩ => exact repair12229Cell39
  | ⟨40,_⟩ => exact repair12229Cell40
  | ⟨41,_⟩ => exact repair12229Cell41
  | ⟨42,_⟩ => exact repair12229Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12229 : FrameRepair 12229 scalarRow12229 where
  cap := cap12229
  cap_nonneg := fun j => (repair12229Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12229])
  endpoint := fun j => (repair12229Cells j).2.1
  endpoint_upper := fun j => (repair12229Cells j).2.2.1
  frame := fun j => (repair12229Cells j).2.2.2

noncomputable def cap12230 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976177 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276355593 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138378919 / 500000000 : ℝ)
  | ⟨3,_⟩ => (69289771 / 250000000 : ℝ)
  | ⟨4,_⟩ => (138779669 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277958603 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55671281 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278753701 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279150019 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55909073 / 200000000 : ℝ)
  | ⟨10,_⟩ => (279939739 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (35041583 / 125000000 : ℝ)
  | ⟨12,_⟩ => (28072511 / 100000000 : ℝ)
  | ⟨13,_⟩ => (281116109 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (1759419 / 6250000 : ℝ)
  | ⟨15,_⟩ => (28189687 / 100000000 : ℝ)
  | ⟨16,_⟩ => (70571439 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282673711 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (11322429 / 40000000 : ℝ)
  | ⟨19,_⟩ => (28344681 / 100000000 : ℝ)
  | ⟨20,_⟩ => (283831967 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284216207 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142299761 / 500000000 : ℝ)
  | ⟨23,_⟩ => (142490713 / 500000000 : ℝ)
  | ⟨24,_⟩ => (71340729 / 250000000 : ℝ)
  | ⟨25,_⟩ => (71435761 / 250000000 : ℝ)
  | ⟨26,_⟩ => (286122767 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286501089 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (57375703 / 200000000 : ℝ)
  | ⟨29,_⟩ => (71813761 / 250000000 : ℝ)
  | ⟨30,_⟩ => (143815089 / 500000000 : ℝ)
  | ⟨31,_⟩ => (4500077 / 15625000 : ℝ)
  | ⟨32,_⟩ => (72094699 / 250000000 : ℝ)
  | ⟨33,_⟩ => (36093909 / 125000000 : ℝ)
  | ⟨34,_⟩ => (289122873 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144746801 / 500000000 : ℝ)
  | ⟨36,_⟩ => (72465863 / 250000000 : ℝ)
  | ⟨37,_⟩ => (290232443 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (36325071 / 125000000 : ℝ)
  | ⟨39,_⟩ => (7274183 / 25000000 : ℝ)
  | ⟨40,_⟩ => (72833303 / 250000000 : ℝ)
  | ⟨41,_⟩ => (72924563 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292062439 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12230Cell0 :
    0 ≤ cap12230 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨0,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12230 ⟨0,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨0,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell1 :
    0 ≤ cap12230 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨1,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12230 ⟨1,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨1,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell2 :
    0 ≤ cap12230 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨2,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12230 ⟨2,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨2,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell3 :
    0 ≤ cap12230 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨3,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12230 ⟨3,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨3,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell4 :
    0 ≤ cap12230 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨4,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12230 ⟨4,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨4,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell5 :
    0 ≤ cap12230 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨5,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12230 ⟨5,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨5,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell6 :
    0 ≤ cap12230 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨6,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12230 ⟨6,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨6,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell7 :
    0 ≤ cap12230 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨7,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12230 ⟨7,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨7,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell8 :
    0 ≤ cap12230 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨8,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12230 ⟨8,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨8,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell9 :
    0 ≤ cap12230 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨9,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12230 ⟨9,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨9,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell10 :
    0 ≤ cap12230 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨10,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12230 ⟨10,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨10,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell11 :
    0 ≤ cap12230 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨11,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12230 ⟨11,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨11,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell12 :
    0 ≤ cap12230 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨12,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12230 ⟨12,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨12,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell13 :
    0 ≤ cap12230 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨13,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12230 ⟨13,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨13,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell14 :
    0 ≤ cap12230 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨14,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12230 ⟨14,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨14,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell15 :
    0 ≤ cap12230 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨15,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12230 ⟨15,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨15,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell16 :
    0 ≤ cap12230 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨16,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12230 ⟨16,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨16,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell17 :
    0 ≤ cap12230 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨17,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12230 ⟨17,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨17,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell18 :
    0 ≤ cap12230 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨18,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12230 ⟨18,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨18,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell19 :
    0 ≤ cap12230 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨19,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12230 ⟨19,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨19,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell20 :
    0 ≤ cap12230 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨20,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12230 ⟨20,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨20,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell21 :
    0 ≤ cap12230 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨21,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12230 ⟨21,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨21,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell22 :
    0 ≤ cap12230 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨22,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12230 ⟨22,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨22,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell23 :
    0 ≤ cap12230 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨23,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12230 ⟨23,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨23,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell24 :
    0 ≤ cap12230 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨24,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12230 ⟨24,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨24,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell25 :
    0 ≤ cap12230 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨25,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12230 ⟨25,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨25,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell26 :
    0 ≤ cap12230 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨26,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12230 ⟨26,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨26,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell27 :
    0 ≤ cap12230 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨27,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12230 ⟨27,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨27,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell28 :
    0 ≤ cap12230 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨28,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12230 ⟨28,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨28,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell29 :
    0 ≤ cap12230 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨29,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12230 ⟨29,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨29,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell30 :
    0 ≤ cap12230 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨30,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12230 ⟨30,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨30,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell31 :
    0 ≤ cap12230 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨31,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12230 ⟨31,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨31,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell32 :
    0 ≤ cap12230 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨32,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12230 ⟨32,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨32,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell33 :
    0 ≤ cap12230 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨33,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12230 ⟨33,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨33,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell34 :
    0 ≤ cap12230 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨34,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12230 ⟨34,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨34,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell35 :
    0 ≤ cap12230 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨35,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12230 ⟨35,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨35,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell36 :
    0 ≤ cap12230 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨36,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12230 ⟨36,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨36,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell37 :
    0 ≤ cap12230 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨37,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12230 ⟨37,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨37,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell38 :
    0 ≤ cap12230 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨38,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12230 ⟨38,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨38,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell39 :
    0 ≤ cap12230 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨39,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12230 ⟨39,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨39,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell40 :
    0 ≤ cap12230 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨40,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12230 ⟨40,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨40,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell41 :
    0 ≤ cap12230 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨41,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12230 ⟨41,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨41,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cell42 :
    0 ≤ cap12230 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12230 (parameters ⟨42,by decide⟩)
      (scalarRow12230.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12230 ⟨42,by decide⟩ ∧
    (scalarRow12230.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 ⟨42,by decide⟩ + (scalarRow12230.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12230.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12230.targetFrame := by
  norm_num [cap12230, scalarRow12230, sourceIndex, cell12230, BstLean.Part263.envelope, parameters]

theorem repair12230Cells (j : Fin 43) :
    0 ≤ cap12230 j ∧
    BstLean.Part263.envelope 12230 (parameters j) (scalarRow12230.table (sourceIndex j)).upper ≤ cap12230 j ∧
    (scalarRow12230.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12230 j + (scalarRow12230.table (sourceIndex j)).centre) /
      (scalarRow12230.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12230.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12230Cell0
  | ⟨1,_⟩ => exact repair12230Cell1
  | ⟨2,_⟩ => exact repair12230Cell2
  | ⟨3,_⟩ => exact repair12230Cell3
  | ⟨4,_⟩ => exact repair12230Cell4
  | ⟨5,_⟩ => exact repair12230Cell5
  | ⟨6,_⟩ => exact repair12230Cell6
  | ⟨7,_⟩ => exact repair12230Cell7
  | ⟨8,_⟩ => exact repair12230Cell8
  | ⟨9,_⟩ => exact repair12230Cell9
  | ⟨10,_⟩ => exact repair12230Cell10
  | ⟨11,_⟩ => exact repair12230Cell11
  | ⟨12,_⟩ => exact repair12230Cell12
  | ⟨13,_⟩ => exact repair12230Cell13
  | ⟨14,_⟩ => exact repair12230Cell14
  | ⟨15,_⟩ => exact repair12230Cell15
  | ⟨16,_⟩ => exact repair12230Cell16
  | ⟨17,_⟩ => exact repair12230Cell17
  | ⟨18,_⟩ => exact repair12230Cell18
  | ⟨19,_⟩ => exact repair12230Cell19
  | ⟨20,_⟩ => exact repair12230Cell20
  | ⟨21,_⟩ => exact repair12230Cell21
  | ⟨22,_⟩ => exact repair12230Cell22
  | ⟨23,_⟩ => exact repair12230Cell23
  | ⟨24,_⟩ => exact repair12230Cell24
  | ⟨25,_⟩ => exact repair12230Cell25
  | ⟨26,_⟩ => exact repair12230Cell26
  | ⟨27,_⟩ => exact repair12230Cell27
  | ⟨28,_⟩ => exact repair12230Cell28
  | ⟨29,_⟩ => exact repair12230Cell29
  | ⟨30,_⟩ => exact repair12230Cell30
  | ⟨31,_⟩ => exact repair12230Cell31
  | ⟨32,_⟩ => exact repair12230Cell32
  | ⟨33,_⟩ => exact repair12230Cell33
  | ⟨34,_⟩ => exact repair12230Cell34
  | ⟨35,_⟩ => exact repair12230Cell35
  | ⟨36,_⟩ => exact repair12230Cell36
  | ⟨37,_⟩ => exact repair12230Cell37
  | ⟨38,_⟩ => exact repair12230Cell38
  | ⟨39,_⟩ => exact repair12230Cell39
  | ⟨40,_⟩ => exact repair12230Cell40
  | ⟨41,_⟩ => exact repair12230Cell41
  | ⟨42,_⟩ => exact repair12230Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12230 : FrameRepair 12230 scalarRow12230 where
  cap := cap12230
  cap_nonneg := fun j => (repair12230Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12230])
  endpoint := fun j => (repair12230Cells j).2.1
  endpoint_upper := fun j => (repair12230Cells j).2.2.1
  frame := fun j => (repair12230Cells j).2.2.2

noncomputable def cap12231 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976139 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276355511 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276757749 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (69289747 / 250000000 : ℝ)
  | ⟨4,_⟩ => (69389809 / 250000000 : ℝ)
  | ⟨5,_⟩ => (138979247 / 500000000 : ℝ)
  | ⟨6,_⟩ => (27835629 / 100000000 : ℝ)
  | ⟨7,_⟩ => (278753579 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (69787473 / 250000000 : ℝ)
  | ⟨9,_⟩ => (279545231 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279939599 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280332517 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280724957 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281115949 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140753437 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281896697 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (141142789 / 500000000 : ℝ)
  | ⟨17,_⟩ => (141336763 / 500000000 : ℝ)
  | ⟨18,_⟩ => (141530267 / 500000000 : ℝ)
  | ⟨19,_⟩ => (70861653 / 250000000 : ℝ)
  | ⟨20,_⟩ => (283831763 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284215997 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142299653 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284981203 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285362687 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285742809 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (11444901 / 40000000 : ℝ)
  | ⟨27,_⟩ => (143250421 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286878261 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (1122089 / 3906250 : ℝ)
  | ⟨30,_⟩ => (35953739 / 125000000 : ℝ)
  | ⟨31,_⟩ => (18000291 / 62500000 : ℝ)
  | ⟨32,_⟩ => (288378517 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72187747 / 250000000 : ℝ)
  | ⟨34,_⟩ => (289122583 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (57898661 / 200000000 : ℝ)
  | ⟨36,_⟩ => (5797263 / 20000000 : ℝ)
  | ⟨37,_⟩ => (58046427 / 200000000 : ℝ)
  | ⟨38,_⟩ => (145300127 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290966999 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58266577 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291697919 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (2920621 / 10000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12231Cell0 :
    0 ≤ cap12231 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨0,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12231 ⟨0,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨0,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell1 :
    0 ≤ cap12231 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨1,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12231 ⟨1,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨1,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell2 :
    0 ≤ cap12231 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨2,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12231 ⟨2,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨2,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell3 :
    0 ≤ cap12231 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨3,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12231 ⟨3,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨3,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell4 :
    0 ≤ cap12231 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨4,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12231 ⟨4,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨4,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell5 :
    0 ≤ cap12231 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨5,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12231 ⟨5,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨5,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell6 :
    0 ≤ cap12231 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨6,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12231 ⟨6,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨6,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell7 :
    0 ≤ cap12231 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨7,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12231 ⟨7,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨7,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell8 :
    0 ≤ cap12231 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨8,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12231 ⟨8,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨8,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell9 :
    0 ≤ cap12231 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨9,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12231 ⟨9,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨9,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell10 :
    0 ≤ cap12231 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨10,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12231 ⟨10,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨10,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell11 :
    0 ≤ cap12231 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨11,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12231 ⟨11,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨11,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell12 :
    0 ≤ cap12231 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨12,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12231 ⟨12,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨12,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell13 :
    0 ≤ cap12231 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨13,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12231 ⟨13,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨13,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell14 :
    0 ≤ cap12231 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨14,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12231 ⟨14,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨14,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell15 :
    0 ≤ cap12231 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨15,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12231 ⟨15,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨15,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell16 :
    0 ≤ cap12231 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨16,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12231 ⟨16,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨16,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell17 :
    0 ≤ cap12231 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨17,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12231 ⟨17,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨17,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell18 :
    0 ≤ cap12231 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨18,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12231 ⟨18,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨18,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell19 :
    0 ≤ cap12231 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨19,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12231 ⟨19,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨19,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell20 :
    0 ≤ cap12231 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨20,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12231 ⟨20,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨20,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell21 :
    0 ≤ cap12231 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨21,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12231 ⟨21,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨21,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell22 :
    0 ≤ cap12231 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨22,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12231 ⟨22,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨22,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell23 :
    0 ≤ cap12231 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨23,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12231 ⟨23,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨23,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell24 :
    0 ≤ cap12231 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨24,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12231 ⟨24,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨24,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell25 :
    0 ≤ cap12231 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨25,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12231 ⟨25,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨25,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell26 :
    0 ≤ cap12231 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨26,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12231 ⟨26,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨26,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell27 :
    0 ≤ cap12231 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨27,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12231 ⟨27,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨27,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell28 :
    0 ≤ cap12231 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨28,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12231 ⟨28,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨28,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell29 :
    0 ≤ cap12231 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨29,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12231 ⟨29,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨29,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell30 :
    0 ≤ cap12231 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨30,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12231 ⟨30,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨30,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell31 :
    0 ≤ cap12231 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨31,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12231 ⟨31,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨31,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell32 :
    0 ≤ cap12231 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨32,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12231 ⟨32,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨32,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell33 :
    0 ≤ cap12231 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨33,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12231 ⟨33,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨33,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell34 :
    0 ≤ cap12231 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨34,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12231 ⟨34,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨34,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell35 :
    0 ≤ cap12231 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨35,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12231 ⟨35,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨35,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell36 :
    0 ≤ cap12231 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨36,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12231 ⟨36,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨36,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell37 :
    0 ≤ cap12231 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨37,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12231 ⟨37,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨37,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell38 :
    0 ≤ cap12231 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨38,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12231 ⟨38,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨38,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell39 :
    0 ≤ cap12231 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨39,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12231 ⟨39,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨39,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell40 :
    0 ≤ cap12231 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨40,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12231 ⟨40,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨40,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell41 :
    0 ≤ cap12231 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨41,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12231 ⟨41,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨41,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cell42 :
    0 ≤ cap12231 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12231 (parameters ⟨42,by decide⟩)
      (scalarRow12231.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12231 ⟨42,by decide⟩ ∧
    (scalarRow12231.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 ⟨42,by decide⟩ + (scalarRow12231.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12231.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12231.targetFrame := by
  norm_num [cap12231, scalarRow12231, sourceIndex, cell12231, BstLean.Part263.envelope, parameters]

theorem repair12231Cells (j : Fin 43) :
    0 ≤ cap12231 j ∧
    BstLean.Part263.envelope 12231 (parameters j) (scalarRow12231.table (sourceIndex j)).upper ≤ cap12231 j ∧
    (scalarRow12231.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12231 j + (scalarRow12231.table (sourceIndex j)).centre) /
      (scalarRow12231.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12231.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12231Cell0
  | ⟨1,_⟩ => exact repair12231Cell1
  | ⟨2,_⟩ => exact repair12231Cell2
  | ⟨3,_⟩ => exact repair12231Cell3
  | ⟨4,_⟩ => exact repair12231Cell4
  | ⟨5,_⟩ => exact repair12231Cell5
  | ⟨6,_⟩ => exact repair12231Cell6
  | ⟨7,_⟩ => exact repair12231Cell7
  | ⟨8,_⟩ => exact repair12231Cell8
  | ⟨9,_⟩ => exact repair12231Cell9
  | ⟨10,_⟩ => exact repair12231Cell10
  | ⟨11,_⟩ => exact repair12231Cell11
  | ⟨12,_⟩ => exact repair12231Cell12
  | ⟨13,_⟩ => exact repair12231Cell13
  | ⟨14,_⟩ => exact repair12231Cell14
  | ⟨15,_⟩ => exact repair12231Cell15
  | ⟨16,_⟩ => exact repair12231Cell16
  | ⟨17,_⟩ => exact repair12231Cell17
  | ⟨18,_⟩ => exact repair12231Cell18
  | ⟨19,_⟩ => exact repair12231Cell19
  | ⟨20,_⟩ => exact repair12231Cell20
  | ⟨21,_⟩ => exact repair12231Cell21
  | ⟨22,_⟩ => exact repair12231Cell22
  | ⟨23,_⟩ => exact repair12231Cell23
  | ⟨24,_⟩ => exact repair12231Cell24
  | ⟨25,_⟩ => exact repair12231Cell25
  | ⟨26,_⟩ => exact repair12231Cell26
  | ⟨27,_⟩ => exact repair12231Cell27
  | ⟨28,_⟩ => exact repair12231Cell28
  | ⟨29,_⟩ => exact repair12231Cell29
  | ⟨30,_⟩ => exact repair12231Cell30
  | ⟨31,_⟩ => exact repair12231Cell31
  | ⟨32,_⟩ => exact repair12231Cell32
  | ⟨33,_⟩ => exact repair12231Cell33
  | ⟨34,_⟩ => exact repair12231Cell34
  | ⟨35,_⟩ => exact repair12231Cell35
  | ⟨36,_⟩ => exact repair12231Cell36
  | ⟨37,_⟩ => exact repair12231Cell37
  | ⟨38,_⟩ => exact repair12231Cell38
  | ⟨39,_⟩ => exact repair12231Cell39
  | ⟨40,_⟩ => exact repair12231Cell40
  | ⟨41,_⟩ => exact repair12231Cell41
  | ⟨42,_⟩ => exact repair12231Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12231 : FrameRepair 12231 scalarRow12231 where
  cap := cap12231
  cap_nonneg := fun j => (repair12231Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12231])
  endpoint := fun j => (repair12231Cells j).2.1
  endpoint_upper := fun j => (repair12231Cells j).2.2.1
  frame := fun j => (repair12231Cells j).2.2.2

noncomputable def cap12232 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976101 / 500000000 : ℝ)
  | ⟨1,_⟩ => (69088857 / 250000000 : ℝ)
  | ⟨2,_⟩ => (13837883 / 50000000 : ℝ)
  | ⟨3,_⟩ => (69289723 / 250000000 : ℝ)
  | ⟨4,_⟩ => (138779567 / 500000000 : ℝ)
  | ⟨5,_⟩ => (138979193 / 500000000 : ℝ)
  | ⟨6,_⟩ => (11134247 / 40000000 : ℝ)
  | ⟨7,_⟩ => (139376729 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69787441 / 250000000 : ℝ)
  | ⟨9,_⟩ => (279545097 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (139969729 / 500000000 : ℝ)
  | ⟨11,_⟩ => (28033237 / 100000000 : ℝ)
  | ⟨12,_⟩ => (70181201 / 250000000 : ℝ)
  | ⟨13,_⟩ => (28111579 / 100000000 : ℝ)
  | ⟨14,_⟩ => (70376677 / 250000000 : ℝ)
  | ⟨15,_⟩ => (11275861 / 40000000 : ℝ)
  | ⟨16,_⟩ => (282285399 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282673341 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141530171 / 500000000 : ℝ)
  | ⟨19,_⟩ => (56689283 / 200000000 : ℝ)
  | ⟨20,_⟩ => (283831559 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284215787 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284599089 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (14249049 / 50000000 : ℝ)
  | ⟨24,_⟩ => (142681229 / 500000000 : ℝ)
  | ⟨25,_⟩ => (142871287 / 500000000 : ℝ)
  | ⟨26,_⟩ => (71530571 / 250000000 : ℝ)
  | ⟨27,_⟩ => (57300119 / 200000000 : ℝ)
  | ⟨28,_⟩ => (35859751 / 125000000 : ℝ)
  | ⟨29,_⟩ => (71813631 / 250000000 : ℝ)
  | ⟨30,_⟩ => (287629647 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (9000137 / 31250000 : ℝ)
  | ⟨32,_⟩ => (288378239 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (18046919 / 62500000 : ℝ)
  | ⟨34,_⟩ => (289122293 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289493009 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (4529107 / 15625000 : ℝ)
  | ⟨37,_⟩ => (290231827 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290599939 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290966679 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291332559 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291697587 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146030881 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12232Cell0 :
    0 ≤ cap12232 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨0,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12232 ⟨0,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨0,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell1 :
    0 ≤ cap12232 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨1,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12232 ⟨1,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨1,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell2 :
    0 ≤ cap12232 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨2,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12232 ⟨2,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨2,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell3 :
    0 ≤ cap12232 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨3,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12232 ⟨3,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨3,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell4 :
    0 ≤ cap12232 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨4,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12232 ⟨4,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨4,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell5 :
    0 ≤ cap12232 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨5,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12232 ⟨5,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨5,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell6 :
    0 ≤ cap12232 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨6,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12232 ⟨6,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨6,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell7 :
    0 ≤ cap12232 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨7,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12232 ⟨7,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨7,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell8 :
    0 ≤ cap12232 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨8,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12232 ⟨8,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨8,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell9 :
    0 ≤ cap12232 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨9,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12232 ⟨9,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨9,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell10 :
    0 ≤ cap12232 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨10,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12232 ⟨10,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨10,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell11 :
    0 ≤ cap12232 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨11,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12232 ⟨11,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨11,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell12 :
    0 ≤ cap12232 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨12,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12232 ⟨12,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨12,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell13 :
    0 ≤ cap12232 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨13,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12232 ⟨13,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨13,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell14 :
    0 ≤ cap12232 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨14,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12232 ⟨14,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨14,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell15 :
    0 ≤ cap12232 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨15,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12232 ⟨15,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨15,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell16 :
    0 ≤ cap12232 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨16,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12232 ⟨16,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨16,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell17 :
    0 ≤ cap12232 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨17,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12232 ⟨17,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨17,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell18 :
    0 ≤ cap12232 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨18,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12232 ⟨18,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨18,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell19 :
    0 ≤ cap12232 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨19,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12232 ⟨19,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨19,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell20 :
    0 ≤ cap12232 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨20,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12232 ⟨20,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨20,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell21 :
    0 ≤ cap12232 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨21,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12232 ⟨21,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨21,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell22 :
    0 ≤ cap12232 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨22,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12232 ⟨22,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨22,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell23 :
    0 ≤ cap12232 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨23,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12232 ⟨23,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨23,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell24 :
    0 ≤ cap12232 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨24,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12232 ⟨24,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨24,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell25 :
    0 ≤ cap12232 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨25,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12232 ⟨25,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨25,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell26 :
    0 ≤ cap12232 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨26,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12232 ⟨26,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨26,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell27 :
    0 ≤ cap12232 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨27,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12232 ⟨27,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨27,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell28 :
    0 ≤ cap12232 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨28,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12232 ⟨28,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨28,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell29 :
    0 ≤ cap12232 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨29,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12232 ⟨29,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨29,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell30 :
    0 ≤ cap12232 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨30,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12232 ⟨30,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨30,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell31 :
    0 ≤ cap12232 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨31,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12232 ⟨31,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨31,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell32 :
    0 ≤ cap12232 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨32,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12232 ⟨32,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨32,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell33 :
    0 ≤ cap12232 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨33,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12232 ⟨33,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨33,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell34 :
    0 ≤ cap12232 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨34,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12232 ⟨34,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨34,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell35 :
    0 ≤ cap12232 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨35,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12232 ⟨35,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨35,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell36 :
    0 ≤ cap12232 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨36,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12232 ⟨36,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨36,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell37 :
    0 ≤ cap12232 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨37,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12232 ⟨37,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨37,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell38 :
    0 ≤ cap12232 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨38,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12232 ⟨38,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨38,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell39 :
    0 ≤ cap12232 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨39,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12232 ⟨39,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨39,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell40 :
    0 ≤ cap12232 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨40,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12232 ⟨40,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨40,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell41 :
    0 ≤ cap12232 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨41,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12232 ⟨41,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨41,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cell42 :
    0 ≤ cap12232 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12232 (parameters ⟨42,by decide⟩)
      (scalarRow12232.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12232 ⟨42,by decide⟩ ∧
    (scalarRow12232.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 ⟨42,by decide⟩ + (scalarRow12232.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12232.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12232.targetFrame := by
  norm_num [cap12232, scalarRow12232, sourceIndex, cell12232, BstLean.Part263.envelope, parameters]

theorem repair12232Cells (j : Fin 43) :
    0 ≤ cap12232 j ∧
    BstLean.Part263.envelope 12232 (parameters j) (scalarRow12232.table (sourceIndex j)).upper ≤ cap12232 j ∧
    (scalarRow12232.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12232 j + (scalarRow12232.table (sourceIndex j)).centre) /
      (scalarRow12232.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12232.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12232Cell0
  | ⟨1,_⟩ => exact repair12232Cell1
  | ⟨2,_⟩ => exact repair12232Cell2
  | ⟨3,_⟩ => exact repair12232Cell3
  | ⟨4,_⟩ => exact repair12232Cell4
  | ⟨5,_⟩ => exact repair12232Cell5
  | ⟨6,_⟩ => exact repair12232Cell6
  | ⟨7,_⟩ => exact repair12232Cell7
  | ⟨8,_⟩ => exact repair12232Cell8
  | ⟨9,_⟩ => exact repair12232Cell9
  | ⟨10,_⟩ => exact repair12232Cell10
  | ⟨11,_⟩ => exact repair12232Cell11
  | ⟨12,_⟩ => exact repair12232Cell12
  | ⟨13,_⟩ => exact repair12232Cell13
  | ⟨14,_⟩ => exact repair12232Cell14
  | ⟨15,_⟩ => exact repair12232Cell15
  | ⟨16,_⟩ => exact repair12232Cell16
  | ⟨17,_⟩ => exact repair12232Cell17
  | ⟨18,_⟩ => exact repair12232Cell18
  | ⟨19,_⟩ => exact repair12232Cell19
  | ⟨20,_⟩ => exact repair12232Cell20
  | ⟨21,_⟩ => exact repair12232Cell21
  | ⟨22,_⟩ => exact repair12232Cell22
  | ⟨23,_⟩ => exact repair12232Cell23
  | ⟨24,_⟩ => exact repair12232Cell24
  | ⟨25,_⟩ => exact repair12232Cell25
  | ⟨26,_⟩ => exact repair12232Cell26
  | ⟨27,_⟩ => exact repair12232Cell27
  | ⟨28,_⟩ => exact repair12232Cell28
  | ⟨29,_⟩ => exact repair12232Cell29
  | ⟨30,_⟩ => exact repair12232Cell30
  | ⟨31,_⟩ => exact repair12232Cell31
  | ⟨32,_⟩ => exact repair12232Cell32
  | ⟨33,_⟩ => exact repair12232Cell33
  | ⟨34,_⟩ => exact repair12232Cell34
  | ⟨35,_⟩ => exact repair12232Cell35
  | ⟨36,_⟩ => exact repair12232Cell36
  | ⟨37,_⟩ => exact repair12232Cell37
  | ⟨38,_⟩ => exact repair12232Cell38
  | ⟨39,_⟩ => exact repair12232Cell39
  | ⟨40,_⟩ => exact repair12232Cell40
  | ⟨41,_⟩ => exact repair12232Cell41
  | ⟨42,_⟩ => exact repair12232Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12232 : FrameRepair 12232 scalarRow12232 where
  cap := cap12232
  cap_nonneg := fun j => (repair12232Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12232])
  endpoint := fun j => (repair12232Cells j).2.1
  endpoint_upper := fun j => (repair12232Cells j).2.2.1
  frame := fun j => (repair12232Cells j).2.2.2

noncomputable def cap12233 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976063 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138177673 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276757571 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277158797 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (34694879 / 125000000 : ℝ)
  | ⟨5,_⟩ => (277958277 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (13917803 / 50000000 : ℝ)
  | ⟨7,_⟩ => (278753337 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (69787409 / 250000000 : ℝ)
  | ⟨9,_⟩ => (279544963 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279939317 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280332223 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (5614493 / 20000000 : ℝ)
  | ⟨13,_⟩ => (28111563 / 100000000 : ℝ)
  | ⟨14,_⟩ => (140753271 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281896353 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (14114261 / 50000000 : ℝ)
  | ⟨17,_⟩ => (70668289 / 250000000 : ℝ)
  | ⟨18,_⟩ => (283060151 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283446217 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (70957839 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284215577 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284598873 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142490379 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285362229 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285742339 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286122043 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286500347 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143438877 / 500000000 : ℝ)
  | ⟨29,_⟩ => (57450853 / 200000000 : ℝ)
  | ⟨30,_⟩ => (287629381 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (18000257 / 62500000 : ℝ)
  | ⟨32,_⟩ => (288377961 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (14437521 / 50000000 : ℝ)
  | ⟨34,_⟩ => (289122003 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289492713 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144931273 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145115759 / 500000000 : ℝ)
  | ⟨38,_⟩ => (2324797 / 8000000 : ℝ)
  | ⟨39,_⟩ => (290966359 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291332233 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145848627 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292061423 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12233Cell0 :
    0 ≤ cap12233 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨0,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12233 ⟨0,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨0,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell1 :
    0 ≤ cap12233 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨1,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12233 ⟨1,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨1,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell2 :
    0 ≤ cap12233 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨2,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12233 ⟨2,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨2,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell3 :
    0 ≤ cap12233 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨3,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12233 ⟨3,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨3,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell4 :
    0 ≤ cap12233 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨4,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12233 ⟨4,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨4,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell5 :
    0 ≤ cap12233 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨5,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12233 ⟨5,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨5,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell6 :
    0 ≤ cap12233 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨6,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12233 ⟨6,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨6,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell7 :
    0 ≤ cap12233 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨7,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12233 ⟨7,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨7,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell8 :
    0 ≤ cap12233 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨8,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12233 ⟨8,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨8,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell9 :
    0 ≤ cap12233 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨9,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12233 ⟨9,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨9,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell10 :
    0 ≤ cap12233 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨10,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12233 ⟨10,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨10,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell11 :
    0 ≤ cap12233 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨11,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12233 ⟨11,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨11,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell12 :
    0 ≤ cap12233 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨12,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12233 ⟨12,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨12,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell13 :
    0 ≤ cap12233 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨13,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12233 ⟨13,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨13,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell14 :
    0 ≤ cap12233 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨14,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12233 ⟨14,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨14,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell15 :
    0 ≤ cap12233 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨15,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12233 ⟨15,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨15,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell16 :
    0 ≤ cap12233 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨16,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12233 ⟨16,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨16,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell17 :
    0 ≤ cap12233 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨17,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12233 ⟨17,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨17,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell18 :
    0 ≤ cap12233 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨18,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12233 ⟨18,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨18,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell19 :
    0 ≤ cap12233 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨19,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12233 ⟨19,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨19,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell20 :
    0 ≤ cap12233 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨20,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12233 ⟨20,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨20,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell21 :
    0 ≤ cap12233 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨21,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12233 ⟨21,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨21,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell22 :
    0 ≤ cap12233 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨22,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12233 ⟨22,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨22,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell23 :
    0 ≤ cap12233 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨23,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12233 ⟨23,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨23,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell24 :
    0 ≤ cap12233 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨24,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12233 ⟨24,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨24,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell25 :
    0 ≤ cap12233 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨25,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12233 ⟨25,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨25,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell26 :
    0 ≤ cap12233 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨26,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12233 ⟨26,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨26,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell27 :
    0 ≤ cap12233 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨27,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12233 ⟨27,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨27,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell28 :
    0 ≤ cap12233 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨28,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12233 ⟨28,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨28,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell29 :
    0 ≤ cap12233 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨29,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12233 ⟨29,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨29,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell30 :
    0 ≤ cap12233 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨30,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12233 ⟨30,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨30,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell31 :
    0 ≤ cap12233 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨31,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12233 ⟨31,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨31,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell32 :
    0 ≤ cap12233 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨32,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12233 ⟨32,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨32,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell33 :
    0 ≤ cap12233 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨33,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12233 ⟨33,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨33,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell34 :
    0 ≤ cap12233 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨34,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12233 ⟨34,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨34,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell35 :
    0 ≤ cap12233 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨35,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12233 ⟨35,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨35,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell36 :
    0 ≤ cap12233 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨36,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12233 ⟨36,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨36,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell37 :
    0 ≤ cap12233 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨37,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12233 ⟨37,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨37,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell38 :
    0 ≤ cap12233 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨38,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12233 ⟨38,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨38,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell39 :
    0 ≤ cap12233 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨39,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12233 ⟨39,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨39,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell40 :
    0 ≤ cap12233 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨40,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12233 ⟨40,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨40,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell41 :
    0 ≤ cap12233 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨41,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12233 ⟨41,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨41,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cell42 :
    0 ≤ cap12233 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12233 (parameters ⟨42,by decide⟩)
      (scalarRow12233.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12233 ⟨42,by decide⟩ ∧
    (scalarRow12233.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 ⟨42,by decide⟩ + (scalarRow12233.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12233.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12233.targetFrame := by
  norm_num [cap12233, scalarRow12233, sourceIndex, cell12233, BstLean.Part263.envelope, parameters]

theorem repair12233Cells (j : Fin 43) :
    0 ≤ cap12233 j ∧
    BstLean.Part263.envelope 12233 (parameters j) (scalarRow12233.table (sourceIndex j)).upper ≤ cap12233 j ∧
    (scalarRow12233.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12233 j + (scalarRow12233.table (sourceIndex j)).centre) /
      (scalarRow12233.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12233.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12233Cell0
  | ⟨1,_⟩ => exact repair12233Cell1
  | ⟨2,_⟩ => exact repair12233Cell2
  | ⟨3,_⟩ => exact repair12233Cell3
  | ⟨4,_⟩ => exact repair12233Cell4
  | ⟨5,_⟩ => exact repair12233Cell5
  | ⟨6,_⟩ => exact repair12233Cell6
  | ⟨7,_⟩ => exact repair12233Cell7
  | ⟨8,_⟩ => exact repair12233Cell8
  | ⟨9,_⟩ => exact repair12233Cell9
  | ⟨10,_⟩ => exact repair12233Cell10
  | ⟨11,_⟩ => exact repair12233Cell11
  | ⟨12,_⟩ => exact repair12233Cell12
  | ⟨13,_⟩ => exact repair12233Cell13
  | ⟨14,_⟩ => exact repair12233Cell14
  | ⟨15,_⟩ => exact repair12233Cell15
  | ⟨16,_⟩ => exact repair12233Cell16
  | ⟨17,_⟩ => exact repair12233Cell17
  | ⟨18,_⟩ => exact repair12233Cell18
  | ⟨19,_⟩ => exact repair12233Cell19
  | ⟨20,_⟩ => exact repair12233Cell20
  | ⟨21,_⟩ => exact repair12233Cell21
  | ⟨22,_⟩ => exact repair12233Cell22
  | ⟨23,_⟩ => exact repair12233Cell23
  | ⟨24,_⟩ => exact repair12233Cell24
  | ⟨25,_⟩ => exact repair12233Cell25
  | ⟨26,_⟩ => exact repair12233Cell26
  | ⟨27,_⟩ => exact repair12233Cell27
  | ⟨28,_⟩ => exact repair12233Cell28
  | ⟨29,_⟩ => exact repair12233Cell29
  | ⟨30,_⟩ => exact repair12233Cell30
  | ⟨31,_⟩ => exact repair12233Cell31
  | ⟨32,_⟩ => exact repair12233Cell32
  | ⟨33,_⟩ => exact repair12233Cell33
  | ⟨34,_⟩ => exact repair12233Cell34
  | ⟨35,_⟩ => exact repair12233Cell35
  | ⟨36,_⟩ => exact repair12233Cell36
  | ⟨37,_⟩ => exact repair12233Cell37
  | ⟨38,_⟩ => exact repair12233Cell38
  | ⟨39,_⟩ => exact repair12233Cell39
  | ⟨40,_⟩ => exact repair12233Cell40
  | ⟨41,_⟩ => exact repair12233Cell41
  | ⟨42,_⟩ => exact repair12233Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12233 : FrameRepair 12233 scalarRow12233 where
  cap := cap12233
  cap_nonneg := fun j => (repair12233Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12233])
  endpoint := fun j => (repair12233Cells j).2.1
  endpoint_upper := fun j => (repair12233Cells j).2.2.1
  frame := fun j => (repair12233Cells j).2.2.2

noncomputable def cap12234 : Fin 43 → ℝ
  | ⟨0,_⟩ => (5519041 / 20000000 : ℝ)
  | ⟨1,_⟩ => (276355263 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138378741 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277158701 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (27755893 / 100000000 : ℝ)
  | ⟨5,_⟩ => (277958169 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55671189 / 200000000 : ℝ)
  | ⟨7,_⟩ => (55750643 / 200000000 : ℝ)
  | ⟨8,_⟩ => (69787377 / 250000000 : ℝ)
  | ⟨9,_⟩ => (69886207 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279939177 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (70083019 / 250000000 : ℝ)
  | ⟨12,_⟩ => (280724497 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (28111547 / 100000000 : ℝ)
  | ⟨14,_⟩ => (35188297 / 125000000 : ℝ)
  | ⟨15,_⟩ => (14094809 / 50000000 : ℝ)
  | ⟨16,_⟩ => (282285041 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282672971 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (7076499 / 25000000 : ℝ)
  | ⟨19,_⟩ => (14172301 / 50000000 : ℝ)
  | ⟨20,_⟩ => (17739447 / 62500000 : ℝ)
  | ⟨21,_⟩ => (284215367 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284598657 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (56996107 / 200000000 : ℝ)
  | ⟨24,_⟩ => (142681 / 500000 : ℝ)
  | ⟨25,_⟩ => (35717763 / 125000000 : ℝ)
  | ⟨26,_⟩ => (143060901 / 500000000 : ℝ)
  | ⟨27,_⟩ => (2865001 / 10000000 : ℝ)
  | ⟨28,_⟩ => (286877501 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (57450801 / 200000000 : ℝ)
  | ⟨30,_⟩ => (57525823 / 200000000 : ℝ)
  | ⟨31,_⟩ => (225003 / 781250 : ℝ)
  | ⟨32,_⟩ => (72094421 / 250000000 : ℝ)
  | ⟨33,_⟩ => (36093767 / 125000000 : ℝ)
  | ⟨34,_⟩ => (18070107 / 62500000 : ℝ)
  | ⟨35,_⟩ => (289492417 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289862243 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (29023121 / 100000000 : ℝ)
  | ⟨38,_⟩ => (290599311 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145483019 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145665953 / 500000000 : ℝ)
  | ⟨41,_⟩ => (145848461 / 500000000 : ℝ)
  | ⟨42,_⟩ => (58412217 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12234Cell0 :
    0 ≤ cap12234 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨0,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12234 ⟨0,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨0,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell1 :
    0 ≤ cap12234 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨1,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12234 ⟨1,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨1,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell2 :
    0 ≤ cap12234 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨2,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12234 ⟨2,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨2,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell3 :
    0 ≤ cap12234 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨3,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12234 ⟨3,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨3,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell4 :
    0 ≤ cap12234 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨4,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12234 ⟨4,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨4,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell5 :
    0 ≤ cap12234 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨5,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12234 ⟨5,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨5,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell6 :
    0 ≤ cap12234 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨6,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12234 ⟨6,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨6,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell7 :
    0 ≤ cap12234 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨7,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12234 ⟨7,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨7,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell8 :
    0 ≤ cap12234 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨8,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12234 ⟨8,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨8,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell9 :
    0 ≤ cap12234 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨9,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12234 ⟨9,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨9,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell10 :
    0 ≤ cap12234 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨10,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12234 ⟨10,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨10,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell11 :
    0 ≤ cap12234 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨11,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12234 ⟨11,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨11,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell12 :
    0 ≤ cap12234 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨12,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12234 ⟨12,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨12,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell13 :
    0 ≤ cap12234 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨13,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12234 ⟨13,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨13,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell14 :
    0 ≤ cap12234 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨14,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12234 ⟨14,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨14,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell15 :
    0 ≤ cap12234 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨15,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12234 ⟨15,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨15,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell16 :
    0 ≤ cap12234 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨16,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12234 ⟨16,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨16,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell17 :
    0 ≤ cap12234 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨17,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12234 ⟨17,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨17,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell18 :
    0 ≤ cap12234 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨18,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12234 ⟨18,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨18,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell19 :
    0 ≤ cap12234 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨19,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12234 ⟨19,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨19,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell20 :
    0 ≤ cap12234 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨20,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12234 ⟨20,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨20,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell21 :
    0 ≤ cap12234 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨21,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12234 ⟨21,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨21,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell22 :
    0 ≤ cap12234 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨22,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12234 ⟨22,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨22,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell23 :
    0 ≤ cap12234 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨23,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12234 ⟨23,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨23,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell24 :
    0 ≤ cap12234 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨24,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12234 ⟨24,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨24,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell25 :
    0 ≤ cap12234 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨25,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12234 ⟨25,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨25,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell26 :
    0 ≤ cap12234 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨26,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12234 ⟨26,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨26,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell27 :
    0 ≤ cap12234 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨27,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12234 ⟨27,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨27,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell28 :
    0 ≤ cap12234 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨28,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12234 ⟨28,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨28,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell29 :
    0 ≤ cap12234 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨29,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12234 ⟨29,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨29,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell30 :
    0 ≤ cap12234 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨30,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12234 ⟨30,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨30,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell31 :
    0 ≤ cap12234 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨31,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12234 ⟨31,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨31,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell32 :
    0 ≤ cap12234 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨32,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12234 ⟨32,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨32,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell33 :
    0 ≤ cap12234 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨33,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12234 ⟨33,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨33,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell34 :
    0 ≤ cap12234 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨34,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12234 ⟨34,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨34,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell35 :
    0 ≤ cap12234 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨35,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12234 ⟨35,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨35,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell36 :
    0 ≤ cap12234 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨36,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12234 ⟨36,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨36,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell37 :
    0 ≤ cap12234 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨37,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12234 ⟨37,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨37,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell38 :
    0 ≤ cap12234 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨38,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12234 ⟨38,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨38,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell39 :
    0 ≤ cap12234 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨39,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12234 ⟨39,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨39,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell40 :
    0 ≤ cap12234 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨40,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12234 ⟨40,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨40,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell41 :
    0 ≤ cap12234 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨41,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12234 ⟨41,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨41,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cell42 :
    0 ≤ cap12234 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12234 (parameters ⟨42,by decide⟩)
      (scalarRow12234.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12234 ⟨42,by decide⟩ ∧
    (scalarRow12234.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 ⟨42,by decide⟩ + (scalarRow12234.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12234.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12234.targetFrame := by
  norm_num [cap12234, scalarRow12234, sourceIndex, cell12234, BstLean.Part263.envelope, parameters]

theorem repair12234Cells (j : Fin 43) :
    0 ≤ cap12234 j ∧
    BstLean.Part263.envelope 12234 (parameters j) (scalarRow12234.table (sourceIndex j)).upper ≤ cap12234 j ∧
    (scalarRow12234.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12234 j + (scalarRow12234.table (sourceIndex j)).centre) /
      (scalarRow12234.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12234.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12234Cell0
  | ⟨1,_⟩ => exact repair12234Cell1
  | ⟨2,_⟩ => exact repair12234Cell2
  | ⟨3,_⟩ => exact repair12234Cell3
  | ⟨4,_⟩ => exact repair12234Cell4
  | ⟨5,_⟩ => exact repair12234Cell5
  | ⟨6,_⟩ => exact repair12234Cell6
  | ⟨7,_⟩ => exact repair12234Cell7
  | ⟨8,_⟩ => exact repair12234Cell8
  | ⟨9,_⟩ => exact repair12234Cell9
  | ⟨10,_⟩ => exact repair12234Cell10
  | ⟨11,_⟩ => exact repair12234Cell11
  | ⟨12,_⟩ => exact repair12234Cell12
  | ⟨13,_⟩ => exact repair12234Cell13
  | ⟨14,_⟩ => exact repair12234Cell14
  | ⟨15,_⟩ => exact repair12234Cell15
  | ⟨16,_⟩ => exact repair12234Cell16
  | ⟨17,_⟩ => exact repair12234Cell17
  | ⟨18,_⟩ => exact repair12234Cell18
  | ⟨19,_⟩ => exact repair12234Cell19
  | ⟨20,_⟩ => exact repair12234Cell20
  | ⟨21,_⟩ => exact repair12234Cell21
  | ⟨22,_⟩ => exact repair12234Cell22
  | ⟨23,_⟩ => exact repair12234Cell23
  | ⟨24,_⟩ => exact repair12234Cell24
  | ⟨25,_⟩ => exact repair12234Cell25
  | ⟨26,_⟩ => exact repair12234Cell26
  | ⟨27,_⟩ => exact repair12234Cell27
  | ⟨28,_⟩ => exact repair12234Cell28
  | ⟨29,_⟩ => exact repair12234Cell29
  | ⟨30,_⟩ => exact repair12234Cell30
  | ⟨31,_⟩ => exact repair12234Cell31
  | ⟨32,_⟩ => exact repair12234Cell32
  | ⟨33,_⟩ => exact repair12234Cell33
  | ⟨34,_⟩ => exact repair12234Cell34
  | ⟨35,_⟩ => exact repair12234Cell35
  | ⟨36,_⟩ => exact repair12234Cell36
  | ⟨37,_⟩ => exact repair12234Cell37
  | ⟨38,_⟩ => exact repair12234Cell38
  | ⟨39,_⟩ => exact repair12234Cell39
  | ⟨40,_⟩ => exact repair12234Cell40
  | ⟨41,_⟩ => exact repair12234Cell41
  | ⟨42,_⟩ => exact repair12234Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12234 : FrameRepair 12234 scalarRow12234 where
  cap := cap12234
  cap_nonneg := fun j => (repair12234Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12234])
  endpoint := fun j => (repair12234Cells j).2.1
  endpoint_upper := fun j => (repair12234Cells j).2.2.1
  frame := fun j => (repair12234Cells j).2.2.2

noncomputable def cap12235 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975987 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276355181 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276757393 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138579303 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277558829 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (13897903 / 50000000 : ℝ)
  | ⟨6,_⟩ => (278355831 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139376547 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279149381 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139772347 / 500000000 : ℝ)
  | ⟨10,_⟩ => (69984759 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280331929 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (35090543 / 125000000 : ℝ)
  | ⟨13,_⟩ => (281115311 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (28150621 / 100000000 : ℝ)
  | ⟨15,_⟩ => (35237001 / 125000000 : ℝ)
  | ⟨16,_⟩ => (282284863 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141336393 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283059769 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141722911 / 500000000 : ℝ)
  | ⟨20,_⟩ => (70957737 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284215157 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (7114961 / 25000000 : ℝ)
  | ⟨23,_⟩ => (284980313 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71340443 / 250000000 : ℝ)
  | ⟨25,_⟩ => (285741869 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286121561 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286499853 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286877247 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143626873 / 500000000 : ℝ)
  | ⟨30,_⟩ => (5752577 / 20000000 : ℝ)
  | ⟨31,_⟩ => (18000223 / 62500000 : ℝ)
  | ⟨32,_⟩ => (144188703 / 500000000 : ℝ)
  | ⟨33,_⟩ => (72187463 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144560711 / 500000000 : ℝ)
  | ⟨35,_⟩ => (7237303 / 25000000 : ℝ)
  | ⟨36,_⟩ => (289861941 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145115451 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72649749 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145482859 / 500000000 : ℝ)
  | ⟨40,_⟩ => (14566579 / 50000000 : ℝ)
  | ⟨41,_⟩ => (29169659 / 100000000 : ℝ)
  | ⟨42,_⟩ => (292060747 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12235Cell0 :
    0 ≤ cap12235 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨0,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12235 ⟨0,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨0,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell1 :
    0 ≤ cap12235 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨1,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12235 ⟨1,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨1,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell2 :
    0 ≤ cap12235 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨2,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12235 ⟨2,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨2,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell3 :
    0 ≤ cap12235 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨3,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12235 ⟨3,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨3,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell4 :
    0 ≤ cap12235 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨4,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12235 ⟨4,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨4,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell5 :
    0 ≤ cap12235 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨5,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12235 ⟨5,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨5,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell6 :
    0 ≤ cap12235 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨6,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12235 ⟨6,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨6,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell7 :
    0 ≤ cap12235 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨7,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12235 ⟨7,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨7,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell8 :
    0 ≤ cap12235 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨8,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12235 ⟨8,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨8,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell9 :
    0 ≤ cap12235 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨9,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12235 ⟨9,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨9,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell10 :
    0 ≤ cap12235 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨10,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12235 ⟨10,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨10,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell11 :
    0 ≤ cap12235 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨11,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12235 ⟨11,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨11,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell12 :
    0 ≤ cap12235 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨12,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12235 ⟨12,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨12,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell13 :
    0 ≤ cap12235 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨13,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12235 ⟨13,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨13,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell14 :
    0 ≤ cap12235 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨14,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12235 ⟨14,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨14,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell15 :
    0 ≤ cap12235 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨15,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12235 ⟨15,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨15,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell16 :
    0 ≤ cap12235 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨16,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12235 ⟨16,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨16,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell17 :
    0 ≤ cap12235 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨17,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12235 ⟨17,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨17,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell18 :
    0 ≤ cap12235 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨18,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12235 ⟨18,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨18,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell19 :
    0 ≤ cap12235 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨19,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12235 ⟨19,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨19,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell20 :
    0 ≤ cap12235 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨20,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12235 ⟨20,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨20,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell21 :
    0 ≤ cap12235 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨21,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12235 ⟨21,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨21,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell22 :
    0 ≤ cap12235 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨22,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12235 ⟨22,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨22,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell23 :
    0 ≤ cap12235 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨23,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12235 ⟨23,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨23,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell24 :
    0 ≤ cap12235 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨24,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12235 ⟨24,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨24,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell25 :
    0 ≤ cap12235 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨25,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12235 ⟨25,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨25,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell26 :
    0 ≤ cap12235 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨26,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12235 ⟨26,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨26,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell27 :
    0 ≤ cap12235 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨27,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12235 ⟨27,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨27,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell28 :
    0 ≤ cap12235 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨28,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12235 ⟨28,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨28,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell29 :
    0 ≤ cap12235 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨29,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12235 ⟨29,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨29,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell30 :
    0 ≤ cap12235 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨30,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12235 ⟨30,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨30,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell31 :
    0 ≤ cap12235 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨31,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12235 ⟨31,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨31,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell32 :
    0 ≤ cap12235 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨32,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12235 ⟨32,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨32,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell33 :
    0 ≤ cap12235 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨33,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12235 ⟨33,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨33,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell34 :
    0 ≤ cap12235 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨34,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12235 ⟨34,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨34,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell35 :
    0 ≤ cap12235 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨35,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12235 ⟨35,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨35,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell36 :
    0 ≤ cap12235 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨36,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12235 ⟨36,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨36,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell37 :
    0 ≤ cap12235 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨37,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12235 ⟨37,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨37,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell38 :
    0 ≤ cap12235 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨38,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12235 ⟨38,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨38,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell39 :
    0 ≤ cap12235 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨39,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12235 ⟨39,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨39,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell40 :
    0 ≤ cap12235 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨40,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12235 ⟨40,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨40,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell41 :
    0 ≤ cap12235 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨41,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12235 ⟨41,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨41,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cell42 :
    0 ≤ cap12235 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12235 (parameters ⟨42,by decide⟩)
      (scalarRow12235.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12235 ⟨42,by decide⟩ ∧
    (scalarRow12235.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 ⟨42,by decide⟩ + (scalarRow12235.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12235.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12235.targetFrame := by
  norm_num [cap12235, scalarRow12235, sourceIndex, cell12235, BstLean.Part263.envelope, parameters]

theorem repair12235Cells (j : Fin 43) :
    0 ≤ cap12235 j ∧
    BstLean.Part263.envelope 12235 (parameters j) (scalarRow12235.table (sourceIndex j)).upper ≤ cap12235 j ∧
    (scalarRow12235.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12235 j + (scalarRow12235.table (sourceIndex j)).centre) /
      (scalarRow12235.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12235.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12235Cell0
  | ⟨1,_⟩ => exact repair12235Cell1
  | ⟨2,_⟩ => exact repair12235Cell2
  | ⟨3,_⟩ => exact repair12235Cell3
  | ⟨4,_⟩ => exact repair12235Cell4
  | ⟨5,_⟩ => exact repair12235Cell5
  | ⟨6,_⟩ => exact repair12235Cell6
  | ⟨7,_⟩ => exact repair12235Cell7
  | ⟨8,_⟩ => exact repair12235Cell8
  | ⟨9,_⟩ => exact repair12235Cell9
  | ⟨10,_⟩ => exact repair12235Cell10
  | ⟨11,_⟩ => exact repair12235Cell11
  | ⟨12,_⟩ => exact repair12235Cell12
  | ⟨13,_⟩ => exact repair12235Cell13
  | ⟨14,_⟩ => exact repair12235Cell14
  | ⟨15,_⟩ => exact repair12235Cell15
  | ⟨16,_⟩ => exact repair12235Cell16
  | ⟨17,_⟩ => exact repair12235Cell17
  | ⟨18,_⟩ => exact repair12235Cell18
  | ⟨19,_⟩ => exact repair12235Cell19
  | ⟨20,_⟩ => exact repair12235Cell20
  | ⟨21,_⟩ => exact repair12235Cell21
  | ⟨22,_⟩ => exact repair12235Cell22
  | ⟨23,_⟩ => exact repair12235Cell23
  | ⟨24,_⟩ => exact repair12235Cell24
  | ⟨25,_⟩ => exact repair12235Cell25
  | ⟨26,_⟩ => exact repair12235Cell26
  | ⟨27,_⟩ => exact repair12235Cell27
  | ⟨28,_⟩ => exact repair12235Cell28
  | ⟨29,_⟩ => exact repair12235Cell29
  | ⟨30,_⟩ => exact repair12235Cell30
  | ⟨31,_⟩ => exact repair12235Cell31
  | ⟨32,_⟩ => exact repair12235Cell32
  | ⟨33,_⟩ => exact repair12235Cell33
  | ⟨34,_⟩ => exact repair12235Cell34
  | ⟨35,_⟩ => exact repair12235Cell35
  | ⟨36,_⟩ => exact repair12235Cell36
  | ⟨37,_⟩ => exact repair12235Cell37
  | ⟨38,_⟩ => exact repair12235Cell38
  | ⟨39,_⟩ => exact repair12235Cell39
  | ⟨40,_⟩ => exact repair12235Cell40
  | ⟨41,_⟩ => exact repair12235Cell41
  | ⟨42,_⟩ => exact repair12235Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12235 : FrameRepair 12235 scalarRow12235 where
  cap := cap12235
  cap_nonneg := fun j => (repair12235Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12235])
  endpoint := fun j => (repair12235Cells j).2.1
  endpoint_upper := fun j => (repair12235Cells j).2.2.1
  frame := fun j => (repair12235Cells j).2.2.2

noncomputable def cap12236 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975949 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138177549 / 500000000 : ℝ)
  | ⟨2,_⟩ => (34594663 / 125000000 : ℝ)
  | ⟨3,_⟩ => (277158511 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277558727 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (4343093 / 15625000 : ℝ)
  | ⟨6,_⟩ => (69588929 / 250000000 : ℝ)
  | ⟨7,_⟩ => (278752973 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279149253 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (3494307 / 12500000 : ℝ)
  | ⟨10,_⟩ => (17496181 / 62500000 : ℝ)
  | ⟨11,_⟩ => (140165891 / 500000000 : ℝ)
  | ⟨12,_⟩ => (28072419 / 100000000 : ℝ)
  | ⟨13,_⟩ => (281115151 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (70376511 / 250000000 : ℝ)
  | ⟨15,_⟩ => (70473959 / 250000000 : ℝ)
  | ⟨16,_⟩ => (70571171 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282672601 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283059577 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (453513 / 1600000 : ℝ)
  | ⟨20,_⟩ => (35478843 / 125000000 : ℝ)
  | ⟨21,_⟩ => (284214947 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (17787389 / 62500000 : ℝ)
  | ⟨23,_⟩ => (28498009 / 100000000 : ℝ)
  | ⟨24,_⟩ => (285361543 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142870817 / 500000000 : ℝ)
  | ⟨26,_⟩ => (7153033 / 25000000 : ℝ)
  | ⟨27,_⟩ => (143249803 / 500000000 : ℝ)
  | ⟨28,_⟩ => (143438497 / 500000000 : ℝ)
  | ⟨29,_⟩ => (143626743 / 500000000 : ℝ)
  | ⟨30,_⟩ => (35953573 / 125000000 : ℝ)
  | ⟨31,_⟩ => (288003297 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (36047141 / 125000000 : ℝ)
  | ⟨33,_⟩ => (563964 / 1953125 : ℝ)
  | ⟨34,_⟩ => (72280283 / 250000000 : ℝ)
  | ⟨35,_⟩ => (18093239 / 62500000 : ℝ)
  | ⟨36,_⟩ => (289861639 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290230593 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145299341 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145482699 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145665627 / 500000000 : ℝ)
  | ⟨41,_⟩ => (145848129 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292060409 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12236Cell0 :
    0 ≤ cap12236 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨0,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12236 ⟨0,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨0,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell1 :
    0 ≤ cap12236 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨1,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12236 ⟨1,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨1,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell2 :
    0 ≤ cap12236 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨2,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12236 ⟨2,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨2,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell3 :
    0 ≤ cap12236 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨3,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12236 ⟨3,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨3,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell4 :
    0 ≤ cap12236 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨4,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12236 ⟨4,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨4,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell5 :
    0 ≤ cap12236 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨5,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12236 ⟨5,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨5,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell6 :
    0 ≤ cap12236 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨6,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12236 ⟨6,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨6,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell7 :
    0 ≤ cap12236 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨7,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12236 ⟨7,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨7,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell8 :
    0 ≤ cap12236 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨8,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12236 ⟨8,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨8,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell9 :
    0 ≤ cap12236 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨9,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12236 ⟨9,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨9,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell10 :
    0 ≤ cap12236 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨10,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12236 ⟨10,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨10,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell11 :
    0 ≤ cap12236 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨11,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12236 ⟨11,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨11,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell12 :
    0 ≤ cap12236 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨12,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12236 ⟨12,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨12,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell13 :
    0 ≤ cap12236 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨13,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12236 ⟨13,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨13,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell14 :
    0 ≤ cap12236 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨14,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12236 ⟨14,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨14,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell15 :
    0 ≤ cap12236 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨15,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12236 ⟨15,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨15,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell16 :
    0 ≤ cap12236 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨16,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12236 ⟨16,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨16,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell17 :
    0 ≤ cap12236 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨17,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12236 ⟨17,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨17,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell18 :
    0 ≤ cap12236 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨18,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12236 ⟨18,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨18,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell19 :
    0 ≤ cap12236 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨19,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12236 ⟨19,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨19,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell20 :
    0 ≤ cap12236 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨20,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12236 ⟨20,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨20,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell21 :
    0 ≤ cap12236 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨21,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12236 ⟨21,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨21,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell22 :
    0 ≤ cap12236 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨22,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12236 ⟨22,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨22,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell23 :
    0 ≤ cap12236 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨23,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12236 ⟨23,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨23,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell24 :
    0 ≤ cap12236 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨24,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12236 ⟨24,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨24,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell25 :
    0 ≤ cap12236 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨25,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12236 ⟨25,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨25,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell26 :
    0 ≤ cap12236 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨26,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12236 ⟨26,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨26,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell27 :
    0 ≤ cap12236 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨27,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12236 ⟨27,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨27,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell28 :
    0 ≤ cap12236 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨28,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12236 ⟨28,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨28,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell29 :
    0 ≤ cap12236 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨29,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12236 ⟨29,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨29,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell30 :
    0 ≤ cap12236 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨30,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12236 ⟨30,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨30,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell31 :
    0 ≤ cap12236 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨31,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12236 ⟨31,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨31,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell32 :
    0 ≤ cap12236 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨32,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12236 ⟨32,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨32,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell33 :
    0 ≤ cap12236 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨33,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12236 ⟨33,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨33,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell34 :
    0 ≤ cap12236 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨34,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12236 ⟨34,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨34,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell35 :
    0 ≤ cap12236 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨35,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12236 ⟨35,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨35,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell36 :
    0 ≤ cap12236 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨36,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12236 ⟨36,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨36,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell37 :
    0 ≤ cap12236 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨37,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12236 ⟨37,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨37,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell38 :
    0 ≤ cap12236 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨38,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12236 ⟨38,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨38,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell39 :
    0 ≤ cap12236 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨39,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12236 ⟨39,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨39,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell40 :
    0 ≤ cap12236 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨40,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12236 ⟨40,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨40,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell41 :
    0 ≤ cap12236 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨41,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12236 ⟨41,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨41,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cell42 :
    0 ≤ cap12236 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12236 (parameters ⟨42,by decide⟩)
      (scalarRow12236.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12236 ⟨42,by decide⟩ ∧
    (scalarRow12236.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 ⟨42,by decide⟩ + (scalarRow12236.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12236.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12236.targetFrame := by
  norm_num [cap12236, scalarRow12236, sourceIndex, cell12236, BstLean.Part263.envelope, parameters]

theorem repair12236Cells (j : Fin 43) :
    0 ≤ cap12236 j ∧
    BstLean.Part263.envelope 12236 (parameters j) (scalarRow12236.table (sourceIndex j)).upper ≤ cap12236 j ∧
    (scalarRow12236.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12236 j + (scalarRow12236.table (sourceIndex j)).centre) /
      (scalarRow12236.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12236.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12236Cell0
  | ⟨1,_⟩ => exact repair12236Cell1
  | ⟨2,_⟩ => exact repair12236Cell2
  | ⟨3,_⟩ => exact repair12236Cell3
  | ⟨4,_⟩ => exact repair12236Cell4
  | ⟨5,_⟩ => exact repair12236Cell5
  | ⟨6,_⟩ => exact repair12236Cell6
  | ⟨7,_⟩ => exact repair12236Cell7
  | ⟨8,_⟩ => exact repair12236Cell8
  | ⟨9,_⟩ => exact repair12236Cell9
  | ⟨10,_⟩ => exact repair12236Cell10
  | ⟨11,_⟩ => exact repair12236Cell11
  | ⟨12,_⟩ => exact repair12236Cell12
  | ⟨13,_⟩ => exact repair12236Cell13
  | ⟨14,_⟩ => exact repair12236Cell14
  | ⟨15,_⟩ => exact repair12236Cell15
  | ⟨16,_⟩ => exact repair12236Cell16
  | ⟨17,_⟩ => exact repair12236Cell17
  | ⟨18,_⟩ => exact repair12236Cell18
  | ⟨19,_⟩ => exact repair12236Cell19
  | ⟨20,_⟩ => exact repair12236Cell20
  | ⟨21,_⟩ => exact repair12236Cell21
  | ⟨22,_⟩ => exact repair12236Cell22
  | ⟨23,_⟩ => exact repair12236Cell23
  | ⟨24,_⟩ => exact repair12236Cell24
  | ⟨25,_⟩ => exact repair12236Cell25
  | ⟨26,_⟩ => exact repair12236Cell26
  | ⟨27,_⟩ => exact repair12236Cell27
  | ⟨28,_⟩ => exact repair12236Cell28
  | ⟨29,_⟩ => exact repair12236Cell29
  | ⟨30,_⟩ => exact repair12236Cell30
  | ⟨31,_⟩ => exact repair12236Cell31
  | ⟨32,_⟩ => exact repair12236Cell32
  | ⟨33,_⟩ => exact repair12236Cell33
  | ⟨34,_⟩ => exact repair12236Cell34
  | ⟨35,_⟩ => exact repair12236Cell35
  | ⟨36,_⟩ => exact repair12236Cell36
  | ⟨37,_⟩ => exact repair12236Cell37
  | ⟨38,_⟩ => exact repair12236Cell38
  | ⟨39,_⟩ => exact repair12236Cell39
  | ⟨40,_⟩ => exact repair12236Cell40
  | ⟨41,_⟩ => exact repair12236Cell41
  | ⟨42,_⟩ => exact repair12236Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12236 : FrameRepair 12236 scalarRow12236 where
  cap := cap12236
  cap_nonneg := fun j => (repair12236Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12236])
  endpoint := fun j => (repair12236Cells j).2.1
  endpoint_upper := fun j => (repair12236Cells j).2.2.1
  frame := fun j => (repair12236Cells j).2.2.2

noncomputable def cap12237 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975911 / 500000000 : ℝ)
  | ⟨1,_⟩ => (34544377 / 125000000 : ℝ)
  | ⟨2,_⟩ => (55351443 / 200000000 : ℝ)
  | ⟨3,_⟩ => (55431683 / 200000000 : ℝ)
  | ⟨4,_⟩ => (2220469 / 8000000 : ℝ)
  | ⟨5,_⟩ => (69489461 / 250000000 : ℝ)
  | ⟨6,_⟩ => (278355601 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278752851 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (2233193 / 8000000 : ℝ)
  | ⟨9,_⟩ => (139772213 / 500000000 : ℝ)
  | ⟨10,_⟩ => (55987751 / 200000000 : ℝ)
  | ⟨11,_⟩ => (56066327 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280724037 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281114991 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140752939 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281895663 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (141142253 / 500000000 : ℝ)
  | ⟨17,_⟩ => (8833513 / 31250000 : ℝ)
  | ⟨18,_⟩ => (141529693 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283445427 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (14191527 / 50000000 : ℝ)
  | ⟨21,_⟩ => (284214737 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (35574751 / 125000000 : ℝ)
  | ⟨23,_⟩ => (71244967 / 250000000 : ℝ)
  | ⟨24,_⟩ => (142680657 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285741399 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286121079 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143249679 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286876741 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287253227 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143814159 / 500000000 : ℝ)
  | ⟨31,_⟩ => (11520121 / 40000000 : ℝ)
  | ⟨32,_⟩ => (5767537 / 20000000 : ℝ)
  | ⟨33,_⟩ => (72187321 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144560421 / 500000000 : ℝ)
  | ⟨35,_⟩ => (36186441 / 125000000 : ℝ)
  | ⟨36,_⟩ => (289861337 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (58046057 / 200000000 : ℝ)
  | ⟨38,_⟩ => (9081199 / 31250000 : ℝ)
  | ⟨39,_⟩ => (145482539 / 500000000 : ℝ)
  | ⟨40,_⟩ => (18208183 / 62500000 : ℝ)
  | ⟨41,_⟩ => (11667837 / 40000000 : ℝ)
  | ⟨42,_⟩ => (29206007 / 100000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12237Cell0 :
    0 ≤ cap12237 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨0,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12237 ⟨0,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨0,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell1 :
    0 ≤ cap12237 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨1,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12237 ⟨1,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨1,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell2 :
    0 ≤ cap12237 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨2,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12237 ⟨2,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨2,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell3 :
    0 ≤ cap12237 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨3,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12237 ⟨3,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨3,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell4 :
    0 ≤ cap12237 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨4,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12237 ⟨4,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨4,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell5 :
    0 ≤ cap12237 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨5,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12237 ⟨5,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨5,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell6 :
    0 ≤ cap12237 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨6,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12237 ⟨6,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨6,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell7 :
    0 ≤ cap12237 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨7,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12237 ⟨7,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨7,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell8 :
    0 ≤ cap12237 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨8,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12237 ⟨8,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨8,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell9 :
    0 ≤ cap12237 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨9,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12237 ⟨9,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨9,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell10 :
    0 ≤ cap12237 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨10,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12237 ⟨10,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨10,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell11 :
    0 ≤ cap12237 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨11,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12237 ⟨11,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨11,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell12 :
    0 ≤ cap12237 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨12,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12237 ⟨12,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨12,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell13 :
    0 ≤ cap12237 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨13,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12237 ⟨13,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨13,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell14 :
    0 ≤ cap12237 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨14,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12237 ⟨14,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨14,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell15 :
    0 ≤ cap12237 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨15,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12237 ⟨15,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨15,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell16 :
    0 ≤ cap12237 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨16,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12237 ⟨16,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨16,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell17 :
    0 ≤ cap12237 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨17,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12237 ⟨17,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨17,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell18 :
    0 ≤ cap12237 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨18,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12237 ⟨18,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨18,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell19 :
    0 ≤ cap12237 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨19,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12237 ⟨19,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨19,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell20 :
    0 ≤ cap12237 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨20,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12237 ⟨20,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨20,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell21 :
    0 ≤ cap12237 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨21,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12237 ⟨21,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨21,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell22 :
    0 ≤ cap12237 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨22,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12237 ⟨22,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨22,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell23 :
    0 ≤ cap12237 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨23,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12237 ⟨23,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨23,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell24 :
    0 ≤ cap12237 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨24,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12237 ⟨24,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨24,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell25 :
    0 ≤ cap12237 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨25,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12237 ⟨25,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨25,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell26 :
    0 ≤ cap12237 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨26,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12237 ⟨26,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨26,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell27 :
    0 ≤ cap12237 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨27,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12237 ⟨27,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨27,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell28 :
    0 ≤ cap12237 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨28,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12237 ⟨28,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨28,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell29 :
    0 ≤ cap12237 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨29,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12237 ⟨29,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨29,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell30 :
    0 ≤ cap12237 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨30,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12237 ⟨30,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨30,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell31 :
    0 ≤ cap12237 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨31,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12237 ⟨31,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨31,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell32 :
    0 ≤ cap12237 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨32,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12237 ⟨32,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨32,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell33 :
    0 ≤ cap12237 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨33,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12237 ⟨33,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨33,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell34 :
    0 ≤ cap12237 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨34,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12237 ⟨34,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨34,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell35 :
    0 ≤ cap12237 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨35,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12237 ⟨35,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨35,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell36 :
    0 ≤ cap12237 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨36,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12237 ⟨36,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨36,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell37 :
    0 ≤ cap12237 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨37,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12237 ⟨37,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨37,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell38 :
    0 ≤ cap12237 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨38,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12237 ⟨38,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨38,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell39 :
    0 ≤ cap12237 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨39,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12237 ⟨39,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨39,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell40 :
    0 ≤ cap12237 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨40,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12237 ⟨40,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨40,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell41 :
    0 ≤ cap12237 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨41,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12237 ⟨41,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨41,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cell42 :
    0 ≤ cap12237 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12237 (parameters ⟨42,by decide⟩)
      (scalarRow12237.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12237 ⟨42,by decide⟩ ∧
    (scalarRow12237.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 ⟨42,by decide⟩ + (scalarRow12237.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12237.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12237.targetFrame := by
  norm_num [cap12237, scalarRow12237, sourceIndex, cell12237, BstLean.Part263.envelope, parameters]

theorem repair12237Cells (j : Fin 43) :
    0 ≤ cap12237 j ∧
    BstLean.Part263.envelope 12237 (parameters j) (scalarRow12237.table (sourceIndex j)).upper ≤ cap12237 j ∧
    (scalarRow12237.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12237 j + (scalarRow12237.table (sourceIndex j)).centre) /
      (scalarRow12237.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12237.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12237Cell0
  | ⟨1,_⟩ => exact repair12237Cell1
  | ⟨2,_⟩ => exact repair12237Cell2
  | ⟨3,_⟩ => exact repair12237Cell3
  | ⟨4,_⟩ => exact repair12237Cell4
  | ⟨5,_⟩ => exact repair12237Cell5
  | ⟨6,_⟩ => exact repair12237Cell6
  | ⟨7,_⟩ => exact repair12237Cell7
  | ⟨8,_⟩ => exact repair12237Cell8
  | ⟨9,_⟩ => exact repair12237Cell9
  | ⟨10,_⟩ => exact repair12237Cell10
  | ⟨11,_⟩ => exact repair12237Cell11
  | ⟨12,_⟩ => exact repair12237Cell12
  | ⟨13,_⟩ => exact repair12237Cell13
  | ⟨14,_⟩ => exact repair12237Cell14
  | ⟨15,_⟩ => exact repair12237Cell15
  | ⟨16,_⟩ => exact repair12237Cell16
  | ⟨17,_⟩ => exact repair12237Cell17
  | ⟨18,_⟩ => exact repair12237Cell18
  | ⟨19,_⟩ => exact repair12237Cell19
  | ⟨20,_⟩ => exact repair12237Cell20
  | ⟨21,_⟩ => exact repair12237Cell21
  | ⟨22,_⟩ => exact repair12237Cell22
  | ⟨23,_⟩ => exact repair12237Cell23
  | ⟨24,_⟩ => exact repair12237Cell24
  | ⟨25,_⟩ => exact repair12237Cell25
  | ⟨26,_⟩ => exact repair12237Cell26
  | ⟨27,_⟩ => exact repair12237Cell27
  | ⟨28,_⟩ => exact repair12237Cell28
  | ⟨29,_⟩ => exact repair12237Cell29
  | ⟨30,_⟩ => exact repair12237Cell30
  | ⟨31,_⟩ => exact repair12237Cell31
  | ⟨32,_⟩ => exact repair12237Cell32
  | ⟨33,_⟩ => exact repair12237Cell33
  | ⟨34,_⟩ => exact repair12237Cell34
  | ⟨35,_⟩ => exact repair12237Cell35
  | ⟨36,_⟩ => exact repair12237Cell36
  | ⟨37,_⟩ => exact repair12237Cell37
  | ⟨38,_⟩ => exact repair12237Cell38
  | ⟨39,_⟩ => exact repair12237Cell39
  | ⟨40,_⟩ => exact repair12237Cell40
  | ⟨41,_⟩ => exact repair12237Cell41
  | ⟨42,_⟩ => exact repair12237Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12237 : FrameRepair 12237 scalarRow12237 where
  cap := cap12237
  cap_nonneg := fun j => (repair12237Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12237])
  endpoint := fun j => (repair12237Cells j).2.1
  endpoint_upper := fun j => (repair12237Cells j).2.2.1
  frame := fun j => (repair12237Cells j).2.2.2

noncomputable def cap12238 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975873 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276354933 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138378563 / 500000000 : ℝ)
  | ⟨3,_⟩ => (3464479 / 12500000 : ℝ)
  | ⟨4,_⟩ => (277558523 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (55591547 / 200000000 : ℝ)
  | ⟨6,_⟩ => (139177743 / 500000000 : ℝ)
  | ⟨7,_⟩ => (27875273 / 100000000 : ℝ)
  | ⟨8,_⟩ => (139574499 / 500000000 : ℝ)
  | ⟨9,_⟩ => (69886073 / 250000000 : ℝ)
  | ⟨10,_⟩ => (55987723 / 200000000 : ℝ)
  | ⟨11,_⟩ => (280331489 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (70180971 / 250000000 : ℝ)
  | ⟨13,_⟩ => (17569677 / 62500000 : ℝ)
  | ⟨14,_⟩ => (17594107 / 62500000 : ℝ)
  | ⟨15,_⟩ => (281895491 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282284327 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282672231 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (56611839 / 200000000 : ℝ)
  | ⟨19,_⟩ => (28344523 / 100000000 : ℝ)
  | ⟨20,_⟩ => (283830337 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284214527 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (8893681 / 31250000 : ℝ)
  | ⟨23,_⟩ => (142489823 / 500000000 : ℝ)
  | ⟨24,_⟩ => (142680543 / 500000000 : ℝ)
  | ⟨25,_⟩ => (71435291 / 250000000 : ℝ)
  | ⟨26,_⟩ => (143060419 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286499111 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286876487 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287252967 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287628053 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (288002753 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72094143 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288749 / 1000000 : ℝ)
  | ⟨34,_⟩ => (36140069 / 125000000 : ℝ)
  | ⟨35,_⟩ => (9046601 / 31250000 : ℝ)
  | ⟨36,_⟩ => (57972207 / 200000000 : ℝ)
  | ⟨37,_⟩ => (290229977 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145299027 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290964757 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291330601 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291695593 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (73014933 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12238Cell0 :
    0 ≤ cap12238 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨0,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12238 ⟨0,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨0,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell1 :
    0 ≤ cap12238 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨1,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12238 ⟨1,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨1,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell2 :
    0 ≤ cap12238 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨2,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12238 ⟨2,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨2,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell3 :
    0 ≤ cap12238 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨3,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12238 ⟨3,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨3,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell4 :
    0 ≤ cap12238 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨4,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12238 ⟨4,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨4,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell5 :
    0 ≤ cap12238 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨5,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12238 ⟨5,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨5,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell6 :
    0 ≤ cap12238 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨6,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12238 ⟨6,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨6,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell7 :
    0 ≤ cap12238 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨7,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12238 ⟨7,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨7,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell8 :
    0 ≤ cap12238 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨8,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12238 ⟨8,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨8,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell9 :
    0 ≤ cap12238 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨9,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12238 ⟨9,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨9,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell10 :
    0 ≤ cap12238 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨10,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12238 ⟨10,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨10,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell11 :
    0 ≤ cap12238 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨11,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12238 ⟨11,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨11,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell12 :
    0 ≤ cap12238 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨12,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12238 ⟨12,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨12,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell13 :
    0 ≤ cap12238 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨13,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12238 ⟨13,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨13,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell14 :
    0 ≤ cap12238 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨14,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12238 ⟨14,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨14,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell15 :
    0 ≤ cap12238 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨15,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12238 ⟨15,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨15,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell16 :
    0 ≤ cap12238 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨16,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12238 ⟨16,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨16,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell17 :
    0 ≤ cap12238 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨17,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12238 ⟨17,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨17,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell18 :
    0 ≤ cap12238 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨18,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12238 ⟨18,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨18,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell19 :
    0 ≤ cap12238 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨19,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12238 ⟨19,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨19,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell20 :
    0 ≤ cap12238 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨20,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12238 ⟨20,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨20,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell21 :
    0 ≤ cap12238 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨21,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12238 ⟨21,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨21,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell22 :
    0 ≤ cap12238 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨22,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12238 ⟨22,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨22,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell23 :
    0 ≤ cap12238 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨23,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12238 ⟨23,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨23,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell24 :
    0 ≤ cap12238 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨24,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12238 ⟨24,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨24,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell25 :
    0 ≤ cap12238 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨25,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12238 ⟨25,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨25,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell26 :
    0 ≤ cap12238 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨26,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12238 ⟨26,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨26,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell27 :
    0 ≤ cap12238 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨27,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12238 ⟨27,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨27,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell28 :
    0 ≤ cap12238 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨28,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12238 ⟨28,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨28,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell29 :
    0 ≤ cap12238 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨29,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12238 ⟨29,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨29,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell30 :
    0 ≤ cap12238 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨30,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12238 ⟨30,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨30,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell31 :
    0 ≤ cap12238 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨31,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12238 ⟨31,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨31,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell32 :
    0 ≤ cap12238 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨32,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12238 ⟨32,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨32,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell33 :
    0 ≤ cap12238 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨33,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12238 ⟨33,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨33,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell34 :
    0 ≤ cap12238 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨34,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12238 ⟨34,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨34,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell35 :
    0 ≤ cap12238 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨35,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12238 ⟨35,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨35,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell36 :
    0 ≤ cap12238 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨36,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12238 ⟨36,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨36,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell37 :
    0 ≤ cap12238 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨37,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12238 ⟨37,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨37,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell38 :
    0 ≤ cap12238 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨38,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12238 ⟨38,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨38,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell39 :
    0 ≤ cap12238 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨39,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12238 ⟨39,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨39,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell40 :
    0 ≤ cap12238 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨40,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12238 ⟨40,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨40,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell41 :
    0 ≤ cap12238 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨41,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12238 ⟨41,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨41,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cell42 :
    0 ≤ cap12238 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12238 (parameters ⟨42,by decide⟩)
      (scalarRow12238.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12238 ⟨42,by decide⟩ ∧
    (scalarRow12238.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 ⟨42,by decide⟩ + (scalarRow12238.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12238.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12238.targetFrame := by
  norm_num [cap12238, scalarRow12238, sourceIndex, cell12238, BstLean.Part263.envelope, parameters]

theorem repair12238Cells (j : Fin 43) :
    0 ≤ cap12238 j ∧
    BstLean.Part263.envelope 12238 (parameters j) (scalarRow12238.table (sourceIndex j)).upper ≤ cap12238 j ∧
    (scalarRow12238.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12238 j + (scalarRow12238.table (sourceIndex j)).centre) /
      (scalarRow12238.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12238.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12238Cell0
  | ⟨1,_⟩ => exact repair12238Cell1
  | ⟨2,_⟩ => exact repair12238Cell2
  | ⟨3,_⟩ => exact repair12238Cell3
  | ⟨4,_⟩ => exact repair12238Cell4
  | ⟨5,_⟩ => exact repair12238Cell5
  | ⟨6,_⟩ => exact repair12238Cell6
  | ⟨7,_⟩ => exact repair12238Cell7
  | ⟨8,_⟩ => exact repair12238Cell8
  | ⟨9,_⟩ => exact repair12238Cell9
  | ⟨10,_⟩ => exact repair12238Cell10
  | ⟨11,_⟩ => exact repair12238Cell11
  | ⟨12,_⟩ => exact repair12238Cell12
  | ⟨13,_⟩ => exact repair12238Cell13
  | ⟨14,_⟩ => exact repair12238Cell14
  | ⟨15,_⟩ => exact repair12238Cell15
  | ⟨16,_⟩ => exact repair12238Cell16
  | ⟨17,_⟩ => exact repair12238Cell17
  | ⟨18,_⟩ => exact repair12238Cell18
  | ⟨19,_⟩ => exact repair12238Cell19
  | ⟨20,_⟩ => exact repair12238Cell20
  | ⟨21,_⟩ => exact repair12238Cell21
  | ⟨22,_⟩ => exact repair12238Cell22
  | ⟨23,_⟩ => exact repair12238Cell23
  | ⟨24,_⟩ => exact repair12238Cell24
  | ⟨25,_⟩ => exact repair12238Cell25
  | ⟨26,_⟩ => exact repair12238Cell26
  | ⟨27,_⟩ => exact repair12238Cell27
  | ⟨28,_⟩ => exact repair12238Cell28
  | ⟨29,_⟩ => exact repair12238Cell29
  | ⟨30,_⟩ => exact repair12238Cell30
  | ⟨31,_⟩ => exact repair12238Cell31
  | ⟨32,_⟩ => exact repair12238Cell32
  | ⟨33,_⟩ => exact repair12238Cell33
  | ⟨34,_⟩ => exact repair12238Cell34
  | ⟨35,_⟩ => exact repair12238Cell35
  | ⟨36,_⟩ => exact repair12238Cell36
  | ⟨37,_⟩ => exact repair12238Cell37
  | ⟨38,_⟩ => exact repair12238Cell38
  | ⟨39,_⟩ => exact repair12238Cell39
  | ⟨40,_⟩ => exact repair12238Cell40
  | ⟨41,_⟩ => exact repair12238Cell41
  | ⟨42,_⟩ => exact repair12238Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12238 : FrameRepair 12238 scalarRow12238 where
  cap := cap12238
  cap_nonneg := fun j => (repair12238Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12238])
  endpoint := fun j => (repair12238Cells j).2.1
  endpoint_upper := fun j => (repair12238Cells j).2.2.1
  frame := fun j => (repair12238Cells j).2.2.2

noncomputable def cap12239 : Fin 43 → ℝ
  | ⟨0,_⟩ => (27595167 / 100000000 : ℝ)
  | ⟨1,_⟩ => (276354851 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276757037 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (17322389 / 62500000 : ℝ)
  | ⟨4,_⟩ => (277558421 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277957627 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278355371 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278752609 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (27914887 / 100000000 : ℝ)
  | ⟨9,_⟩ => (139772079 / 500000000 : ℝ)
  | ⟨10,_⟩ => (139969237 / 500000000 : ℝ)
  | ⟨11,_⟩ => (140165671 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280723731 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (17569667 / 62500000 : ℝ)
  | ⟨14,_⟩ => (140752773 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281895319 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282284149 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141336023 / 500000000 : ℝ)
  | ⟨18,_⟩ => (70764751 / 250000000 : ℝ)
  | ⟨19,_⟩ => (35430629 / 125000000 : ℝ)
  | ⟨20,_⟩ => (283830133 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284214317 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (35574697 / 125000000 : ℝ)
  | ⟨23,_⟩ => (284979423 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285360857 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (28574093 / 100000000 : ℝ)
  | ⟨26,_⟩ => (286120597 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (17906179 / 62500000 : ℝ)
  | ⟨28,_⟩ => (143438117 / 500000000 : ℝ)
  | ⟨29,_⟩ => (71813177 / 250000000 : ℝ)
  | ⟨30,_⟩ => (287627787 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (144001241 / 500000000 : ℝ)
  | ⟨32,_⟩ => (144188147 / 500000000 : ℝ)
  | ⟨33,_⟩ => (72187179 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144560131 / 500000000 : ℝ)
  | ⟨35,_⟩ => (36186367 / 125000000 : ℝ)
  | ⟨36,_⟩ => (289860733 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290229669 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (14529887 / 50000000 : ℝ)
  | ⟨39,_⟩ => (290964437 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (11653211 / 40000000 : ℝ)
  | ⟨41,_⟩ => (291695261 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146029697 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12239Cell0 :
    0 ≤ cap12239 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨0,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12239 ⟨0,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨0,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell1 :
    0 ≤ cap12239 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨1,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12239 ⟨1,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨1,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell2 :
    0 ≤ cap12239 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨2,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12239 ⟨2,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨2,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell3 :
    0 ≤ cap12239 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨3,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12239 ⟨3,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨3,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell4 :
    0 ≤ cap12239 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨4,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12239 ⟨4,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨4,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell5 :
    0 ≤ cap12239 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨5,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12239 ⟨5,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨5,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell6 :
    0 ≤ cap12239 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨6,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12239 ⟨6,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨6,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell7 :
    0 ≤ cap12239 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨7,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12239 ⟨7,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨7,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell8 :
    0 ≤ cap12239 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨8,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12239 ⟨8,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨8,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell9 :
    0 ≤ cap12239 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨9,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12239 ⟨9,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨9,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell10 :
    0 ≤ cap12239 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨10,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12239 ⟨10,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨10,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell11 :
    0 ≤ cap12239 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨11,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12239 ⟨11,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨11,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell12 :
    0 ≤ cap12239 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨12,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12239 ⟨12,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨12,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell13 :
    0 ≤ cap12239 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨13,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12239 ⟨13,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨13,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell14 :
    0 ≤ cap12239 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨14,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12239 ⟨14,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨14,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell15 :
    0 ≤ cap12239 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨15,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12239 ⟨15,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨15,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell16 :
    0 ≤ cap12239 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨16,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12239 ⟨16,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨16,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell17 :
    0 ≤ cap12239 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨17,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12239 ⟨17,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨17,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell18 :
    0 ≤ cap12239 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨18,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12239 ⟨18,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨18,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell19 :
    0 ≤ cap12239 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨19,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12239 ⟨19,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨19,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell20 :
    0 ≤ cap12239 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨20,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12239 ⟨20,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨20,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell21 :
    0 ≤ cap12239 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨21,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12239 ⟨21,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨21,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell22 :
    0 ≤ cap12239 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨22,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12239 ⟨22,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨22,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell23 :
    0 ≤ cap12239 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨23,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12239 ⟨23,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨23,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell24 :
    0 ≤ cap12239 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨24,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12239 ⟨24,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨24,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell25 :
    0 ≤ cap12239 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨25,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12239 ⟨25,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨25,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell26 :
    0 ≤ cap12239 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨26,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12239 ⟨26,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨26,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell27 :
    0 ≤ cap12239 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨27,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12239 ⟨27,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨27,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell28 :
    0 ≤ cap12239 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨28,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12239 ⟨28,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨28,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell29 :
    0 ≤ cap12239 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨29,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12239 ⟨29,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨29,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell30 :
    0 ≤ cap12239 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨30,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12239 ⟨30,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨30,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell31 :
    0 ≤ cap12239 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨31,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12239 ⟨31,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨31,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell32 :
    0 ≤ cap12239 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨32,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12239 ⟨32,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨32,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell33 :
    0 ≤ cap12239 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨33,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12239 ⟨33,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨33,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell34 :
    0 ≤ cap12239 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨34,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12239 ⟨34,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨34,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell35 :
    0 ≤ cap12239 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨35,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12239 ⟨35,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨35,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell36 :
    0 ≤ cap12239 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨36,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12239 ⟨36,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨36,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell37 :
    0 ≤ cap12239 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨37,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12239 ⟨37,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨37,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell38 :
    0 ≤ cap12239 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨38,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12239 ⟨38,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨38,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell39 :
    0 ≤ cap12239 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨39,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12239 ⟨39,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨39,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell40 :
    0 ≤ cap12239 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨40,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12239 ⟨40,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨40,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell41 :
    0 ≤ cap12239 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨41,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12239 ⟨41,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨41,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cell42 :
    0 ≤ cap12239 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12239 (parameters ⟨42,by decide⟩)
      (scalarRow12239.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12239 ⟨42,by decide⟩ ∧
    (scalarRow12239.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 ⟨42,by decide⟩ + (scalarRow12239.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12239.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12239.targetFrame := by
  norm_num [cap12239, scalarRow12239, sourceIndex, cell12239, BstLean.Part263.envelope, parameters]

theorem repair12239Cells (j : Fin 43) :
    0 ≤ cap12239 j ∧
    BstLean.Part263.envelope 12239 (parameters j) (scalarRow12239.table (sourceIndex j)).upper ≤ cap12239 j ∧
    (scalarRow12239.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12239 j + (scalarRow12239.table (sourceIndex j)).centre) /
      (scalarRow12239.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12239.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12239Cell0
  | ⟨1,_⟩ => exact repair12239Cell1
  | ⟨2,_⟩ => exact repair12239Cell2
  | ⟨3,_⟩ => exact repair12239Cell3
  | ⟨4,_⟩ => exact repair12239Cell4
  | ⟨5,_⟩ => exact repair12239Cell5
  | ⟨6,_⟩ => exact repair12239Cell6
  | ⟨7,_⟩ => exact repair12239Cell7
  | ⟨8,_⟩ => exact repair12239Cell8
  | ⟨9,_⟩ => exact repair12239Cell9
  | ⟨10,_⟩ => exact repair12239Cell10
  | ⟨11,_⟩ => exact repair12239Cell11
  | ⟨12,_⟩ => exact repair12239Cell12
  | ⟨13,_⟩ => exact repair12239Cell13
  | ⟨14,_⟩ => exact repair12239Cell14
  | ⟨15,_⟩ => exact repair12239Cell15
  | ⟨16,_⟩ => exact repair12239Cell16
  | ⟨17,_⟩ => exact repair12239Cell17
  | ⟨18,_⟩ => exact repair12239Cell18
  | ⟨19,_⟩ => exact repair12239Cell19
  | ⟨20,_⟩ => exact repair12239Cell20
  | ⟨21,_⟩ => exact repair12239Cell21
  | ⟨22,_⟩ => exact repair12239Cell22
  | ⟨23,_⟩ => exact repair12239Cell23
  | ⟨24,_⟩ => exact repair12239Cell24
  | ⟨25,_⟩ => exact repair12239Cell25
  | ⟨26,_⟩ => exact repair12239Cell26
  | ⟨27,_⟩ => exact repair12239Cell27
  | ⟨28,_⟩ => exact repair12239Cell28
  | ⟨29,_⟩ => exact repair12239Cell29
  | ⟨30,_⟩ => exact repair12239Cell30
  | ⟨31,_⟩ => exact repair12239Cell31
  | ⟨32,_⟩ => exact repair12239Cell32
  | ⟨33,_⟩ => exact repair12239Cell33
  | ⟨34,_⟩ => exact repair12239Cell34
  | ⟨35,_⟩ => exact repair12239Cell35
  | ⟨36,_⟩ => exact repair12239Cell36
  | ⟨37,_⟩ => exact repair12239Cell37
  | ⟨38,_⟩ => exact repair12239Cell38
  | ⟨39,_⟩ => exact repair12239Cell39
  | ⟨40,_⟩ => exact repair12239Cell40
  | ⟨41,_⟩ => exact repair12239Cell41
  | ⟨42,_⟩ => exact repair12239Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12239 : FrameRepair 12239 scalarRow12239 where
  cap := cap12239
  cap_nonneg := fun j => (repair12239Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12239])
  endpoint := fun j => (repair12239Cells j).2.1
  endpoint_upper := fun j => (repair12239Cells j).2.2.1
  frame := fun j => (repair12239Cells j).2.2.2

noncomputable def cap12240 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975797 / 500000000 : ℝ)
  | ⟨1,_⟩ => (17272173 / 62500000 : ℝ)
  | ⟨2,_⟩ => (69189237 / 250000000 : ℝ)
  | ⟨3,_⟩ => (277158129 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277558319 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138978759 / 500000000 : ℝ)
  | ⟨6,_⟩ => (34794407 / 125000000 : ℝ)
  | ⟨7,_⟩ => (34844061 / 125000000 : ℝ)
  | ⟨8,_⟩ => (139574371 / 500000000 : ℝ)
  | ⟨9,_⟩ => (34943003 / 125000000 : ℝ)
  | ⟨10,_⟩ => (139969167 / 500000000 : ℝ)
  | ⟨11,_⟩ => (56066239 / 200000000 : ℝ)
  | ⟨12,_⟩ => (140361789 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281114513 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (14075269 / 50000000 : ℝ)
  | ⟨15,_⟩ => (281895147 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (28228397 / 100000000 : ℝ)
  | ⟨17,_⟩ => (282671861 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283058813 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (56688967 / 200000000 : ℝ)
  | ⟨20,_⟩ => (283829929 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284214107 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (3557467 / 12500000 : ℝ)
  | ⟨23,_⟩ => (284979201 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285360629 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (57148139 / 200000000 : ℝ)
  | ⟨26,_⟩ => (71530089 / 250000000 : ℝ)
  | ⟨27,_⟩ => (286498617 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286875981 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (8976639 / 31250000 : ℝ)
  | ⟨30,_⟩ => (143813761 / 500000000 : ℝ)
  | ⟨31,_⟩ => (28800221 / 100000000 : ℝ)
  | ⟨32,_⟩ => (288376017 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (18046777 / 62500000 : ℝ)
  | ⟨34,_⟩ => (72279993 / 250000000 : ℝ)
  | ⟨35,_⟩ => (3618633 / 12500000 : ℝ)
  | ⟨36,_⟩ => (289860431 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290229361 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145298713 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290964117 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291329949 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291694929 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (18253691 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12240Cell0 :
    0 ≤ cap12240 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨0,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12240 ⟨0,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨0,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell1 :
    0 ≤ cap12240 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨1,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12240 ⟨1,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨1,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell2 :
    0 ≤ cap12240 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨2,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12240 ⟨2,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨2,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell3 :
    0 ≤ cap12240 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨3,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12240 ⟨3,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨3,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell4 :
    0 ≤ cap12240 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨4,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12240 ⟨4,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨4,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell5 :
    0 ≤ cap12240 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨5,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12240 ⟨5,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨5,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell6 :
    0 ≤ cap12240 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨6,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12240 ⟨6,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨6,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell7 :
    0 ≤ cap12240 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨7,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12240 ⟨7,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨7,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell8 :
    0 ≤ cap12240 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨8,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12240 ⟨8,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨8,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell9 :
    0 ≤ cap12240 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨9,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12240 ⟨9,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨9,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell10 :
    0 ≤ cap12240 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨10,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12240 ⟨10,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨10,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell11 :
    0 ≤ cap12240 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨11,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12240 ⟨11,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨11,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell12 :
    0 ≤ cap12240 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨12,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12240 ⟨12,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨12,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell13 :
    0 ≤ cap12240 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨13,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12240 ⟨13,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨13,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell14 :
    0 ≤ cap12240 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨14,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12240 ⟨14,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨14,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell15 :
    0 ≤ cap12240 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨15,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12240 ⟨15,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨15,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell16 :
    0 ≤ cap12240 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨16,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12240 ⟨16,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨16,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell17 :
    0 ≤ cap12240 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨17,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12240 ⟨17,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨17,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell18 :
    0 ≤ cap12240 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨18,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12240 ⟨18,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨18,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell19 :
    0 ≤ cap12240 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨19,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12240 ⟨19,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨19,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell20 :
    0 ≤ cap12240 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨20,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12240 ⟨20,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨20,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell21 :
    0 ≤ cap12240 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨21,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12240 ⟨21,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨21,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell22 :
    0 ≤ cap12240 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨22,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12240 ⟨22,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨22,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell23 :
    0 ≤ cap12240 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨23,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12240 ⟨23,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨23,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell24 :
    0 ≤ cap12240 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨24,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12240 ⟨24,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨24,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell25 :
    0 ≤ cap12240 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨25,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12240 ⟨25,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨25,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell26 :
    0 ≤ cap12240 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨26,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12240 ⟨26,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨26,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell27 :
    0 ≤ cap12240 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨27,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12240 ⟨27,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨27,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell28 :
    0 ≤ cap12240 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨28,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12240 ⟨28,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨28,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell29 :
    0 ≤ cap12240 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨29,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12240 ⟨29,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨29,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell30 :
    0 ≤ cap12240 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨30,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12240 ⟨30,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨30,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell31 :
    0 ≤ cap12240 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨31,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12240 ⟨31,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨31,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell32 :
    0 ≤ cap12240 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨32,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12240 ⟨32,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨32,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell33 :
    0 ≤ cap12240 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨33,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12240 ⟨33,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨33,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell34 :
    0 ≤ cap12240 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨34,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12240 ⟨34,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨34,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell35 :
    0 ≤ cap12240 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨35,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12240 ⟨35,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨35,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell36 :
    0 ≤ cap12240 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨36,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12240 ⟨36,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨36,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell37 :
    0 ≤ cap12240 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨37,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12240 ⟨37,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨37,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell38 :
    0 ≤ cap12240 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨38,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12240 ⟨38,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨38,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell39 :
    0 ≤ cap12240 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨39,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12240 ⟨39,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨39,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell40 :
    0 ≤ cap12240 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨40,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12240 ⟨40,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨40,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell41 :
    0 ≤ cap12240 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨41,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12240 ⟨41,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨41,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cell42 :
    0 ≤ cap12240 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12240 (parameters ⟨42,by decide⟩)
      (scalarRow12240.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12240 ⟨42,by decide⟩ ∧
    (scalarRow12240.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 ⟨42,by decide⟩ + (scalarRow12240.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12240.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12240.targetFrame := by
  norm_num [cap12240, scalarRow12240, sourceIndex, cell12240, BstLean.Part263.envelope, parameters]

theorem repair12240Cells (j : Fin 43) :
    0 ≤ cap12240 j ∧
    BstLean.Part263.envelope 12240 (parameters j) (scalarRow12240.table (sourceIndex j)).upper ≤ cap12240 j ∧
    (scalarRow12240.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12240 j + (scalarRow12240.table (sourceIndex j)).centre) /
      (scalarRow12240.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12240.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12240Cell0
  | ⟨1,_⟩ => exact repair12240Cell1
  | ⟨2,_⟩ => exact repair12240Cell2
  | ⟨3,_⟩ => exact repair12240Cell3
  | ⟨4,_⟩ => exact repair12240Cell4
  | ⟨5,_⟩ => exact repair12240Cell5
  | ⟨6,_⟩ => exact repair12240Cell6
  | ⟨7,_⟩ => exact repair12240Cell7
  | ⟨8,_⟩ => exact repair12240Cell8
  | ⟨9,_⟩ => exact repair12240Cell9
  | ⟨10,_⟩ => exact repair12240Cell10
  | ⟨11,_⟩ => exact repair12240Cell11
  | ⟨12,_⟩ => exact repair12240Cell12
  | ⟨13,_⟩ => exact repair12240Cell13
  | ⟨14,_⟩ => exact repair12240Cell14
  | ⟨15,_⟩ => exact repair12240Cell15
  | ⟨16,_⟩ => exact repair12240Cell16
  | ⟨17,_⟩ => exact repair12240Cell17
  | ⟨18,_⟩ => exact repair12240Cell18
  | ⟨19,_⟩ => exact repair12240Cell19
  | ⟨20,_⟩ => exact repair12240Cell20
  | ⟨21,_⟩ => exact repair12240Cell21
  | ⟨22,_⟩ => exact repair12240Cell22
  | ⟨23,_⟩ => exact repair12240Cell23
  | ⟨24,_⟩ => exact repair12240Cell24
  | ⟨25,_⟩ => exact repair12240Cell25
  | ⟨26,_⟩ => exact repair12240Cell26
  | ⟨27,_⟩ => exact repair12240Cell27
  | ⟨28,_⟩ => exact repair12240Cell28
  | ⟨29,_⟩ => exact repair12240Cell29
  | ⟨30,_⟩ => exact repair12240Cell30
  | ⟨31,_⟩ => exact repair12240Cell31
  | ⟨32,_⟩ => exact repair12240Cell32
  | ⟨33,_⟩ => exact repair12240Cell33
  | ⟨34,_⟩ => exact repair12240Cell34
  | ⟨35,_⟩ => exact repair12240Cell35
  | ⟨36,_⟩ => exact repair12240Cell36
  | ⟨37,_⟩ => exact repair12240Cell37
  | ⟨38,_⟩ => exact repair12240Cell38
  | ⟨39,_⟩ => exact repair12240Cell39
  | ⟨40,_⟩ => exact repair12240Cell40
  | ⟨41,_⟩ => exact repair12240Cell41
  | ⟨42,_⟩ => exact repair12240Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12240 : FrameRepair 12240 scalarRow12240 where
  cap := cap12240
  cap_nonneg := fun j => (repair12240Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12240])
  endpoint := fun j => (repair12240Cells j).2.1
  endpoint_upper := fun j => (repair12240Cells j).2.2.1
  frame := fun j => (repair12240Cells j).2.2.2

noncomputable def cap12241 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975759 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138177343 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276756859 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277158033 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277558217 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (27795741 / 100000000 : ℝ)
  | ⟨6,_⟩ => (139177571 / 500000000 : ℝ)
  | ⟨7,_⟩ => (139376183 / 500000000 : ℝ)
  | ⟨8,_⟩ => (55829723 / 200000000 : ℝ)
  | ⟨9,_⟩ => (27954389 / 100000000 : ℝ)
  | ⟨10,_⟩ => (279938193 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (35041381 / 125000000 : ℝ)
  | ⟨12,_⟩ => (8772607 / 31250000 : ℝ)
  | ⟨13,_⟩ => (281114353 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140752607 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140947487 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282283791 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282671677 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141529311 / 500000000 : ℝ)
  | ⟨19,_⟩ => (141722319 / 500000000 : ℝ)
  | ⟨20,_⟩ => (141914863 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284213897 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284597143 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142489489 / 500000000 : ℝ)
  | ⟨24,_⟩ => (713401 / 2500000 : ℝ)
  | ⟨25,_⟩ => (14287023 / 50000000 : ℝ)
  | ⟨26,_⟩ => (57224023 / 200000000 : ℝ)
  | ⟨27,_⟩ => (28649837 / 100000000 : ℝ)
  | ⟨28,_⟩ => (17929733 / 62500000 : ℝ)
  | ⟨29,_⟩ => (287252189 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (35953407 / 125000000 : ℝ)
  | ⟨31,_⟩ => (144000969 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288375739 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288748149 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289119683 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (36186293 / 125000000 : ℝ)
  | ⟨36,_⟩ => (289860129 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290229053 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (36324639 / 125000000 : ℝ)
  | ⟨39,_⟩ => (290963797 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291329623 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291694597 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146029359 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12241Cell0 :
    0 ≤ cap12241 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨0,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12241 ⟨0,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨0,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell1 :
    0 ≤ cap12241 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨1,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12241 ⟨1,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨1,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell2 :
    0 ≤ cap12241 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨2,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12241 ⟨2,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨2,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell3 :
    0 ≤ cap12241 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨3,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12241 ⟨3,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨3,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell4 :
    0 ≤ cap12241 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨4,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12241 ⟨4,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨4,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell5 :
    0 ≤ cap12241 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨5,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12241 ⟨5,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨5,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell6 :
    0 ≤ cap12241 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨6,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12241 ⟨6,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨6,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell7 :
    0 ≤ cap12241 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨7,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12241 ⟨7,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨7,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell8 :
    0 ≤ cap12241 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨8,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12241 ⟨8,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨8,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell9 :
    0 ≤ cap12241 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨9,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12241 ⟨9,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨9,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell10 :
    0 ≤ cap12241 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨10,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12241 ⟨10,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨10,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell11 :
    0 ≤ cap12241 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨11,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12241 ⟨11,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨11,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell12 :
    0 ≤ cap12241 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨12,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12241 ⟨12,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨12,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell13 :
    0 ≤ cap12241 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨13,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12241 ⟨13,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨13,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell14 :
    0 ≤ cap12241 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨14,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12241 ⟨14,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨14,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell15 :
    0 ≤ cap12241 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨15,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12241 ⟨15,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨15,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell16 :
    0 ≤ cap12241 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨16,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12241 ⟨16,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨16,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell17 :
    0 ≤ cap12241 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨17,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12241 ⟨17,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨17,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell18 :
    0 ≤ cap12241 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨18,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12241 ⟨18,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨18,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell19 :
    0 ≤ cap12241 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨19,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12241 ⟨19,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨19,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell20 :
    0 ≤ cap12241 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨20,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12241 ⟨20,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨20,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell21 :
    0 ≤ cap12241 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨21,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12241 ⟨21,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨21,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell22 :
    0 ≤ cap12241 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨22,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12241 ⟨22,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨22,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell23 :
    0 ≤ cap12241 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨23,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12241 ⟨23,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨23,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell24 :
    0 ≤ cap12241 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨24,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12241 ⟨24,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨24,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell25 :
    0 ≤ cap12241 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨25,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12241 ⟨25,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨25,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell26 :
    0 ≤ cap12241 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨26,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12241 ⟨26,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨26,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell27 :
    0 ≤ cap12241 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨27,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12241 ⟨27,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨27,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell28 :
    0 ≤ cap12241 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨28,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12241 ⟨28,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨28,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell29 :
    0 ≤ cap12241 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨29,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12241 ⟨29,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨29,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell30 :
    0 ≤ cap12241 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨30,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12241 ⟨30,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨30,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell31 :
    0 ≤ cap12241 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨31,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12241 ⟨31,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨31,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell32 :
    0 ≤ cap12241 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨32,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12241 ⟨32,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨32,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell33 :
    0 ≤ cap12241 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨33,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12241 ⟨33,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨33,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell34 :
    0 ≤ cap12241 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨34,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12241 ⟨34,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨34,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell35 :
    0 ≤ cap12241 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨35,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12241 ⟨35,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨35,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell36 :
    0 ≤ cap12241 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨36,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12241 ⟨36,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨36,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell37 :
    0 ≤ cap12241 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨37,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12241 ⟨37,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨37,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell38 :
    0 ≤ cap12241 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨38,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12241 ⟨38,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨38,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell39 :
    0 ≤ cap12241 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨39,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12241 ⟨39,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨39,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell40 :
    0 ≤ cap12241 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨40,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12241 ⟨40,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨40,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell41 :
    0 ≤ cap12241 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨41,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12241 ⟨41,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨41,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cell42 :
    0 ≤ cap12241 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12241 (parameters ⟨42,by decide⟩)
      (scalarRow12241.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12241 ⟨42,by decide⟩ ∧
    (scalarRow12241.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 ⟨42,by decide⟩ + (scalarRow12241.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12241.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12241.targetFrame := by
  norm_num [cap12241, scalarRow12241, sourceIndex, cell12241, BstLean.Part263.envelope, parameters]

theorem repair12241Cells (j : Fin 43) :
    0 ≤ cap12241 j ∧
    BstLean.Part263.envelope 12241 (parameters j) (scalarRow12241.table (sourceIndex j)).upper ≤ cap12241 j ∧
    (scalarRow12241.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12241 j + (scalarRow12241.table (sourceIndex j)).centre) /
      (scalarRow12241.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12241.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12241Cell0
  | ⟨1,_⟩ => exact repair12241Cell1
  | ⟨2,_⟩ => exact repair12241Cell2
  | ⟨3,_⟩ => exact repair12241Cell3
  | ⟨4,_⟩ => exact repair12241Cell4
  | ⟨5,_⟩ => exact repair12241Cell5
  | ⟨6,_⟩ => exact repair12241Cell6
  | ⟨7,_⟩ => exact repair12241Cell7
  | ⟨8,_⟩ => exact repair12241Cell8
  | ⟨9,_⟩ => exact repair12241Cell9
  | ⟨10,_⟩ => exact repair12241Cell10
  | ⟨11,_⟩ => exact repair12241Cell11
  | ⟨12,_⟩ => exact repair12241Cell12
  | ⟨13,_⟩ => exact repair12241Cell13
  | ⟨14,_⟩ => exact repair12241Cell14
  | ⟨15,_⟩ => exact repair12241Cell15
  | ⟨16,_⟩ => exact repair12241Cell16
  | ⟨17,_⟩ => exact repair12241Cell17
  | ⟨18,_⟩ => exact repair12241Cell18
  | ⟨19,_⟩ => exact repair12241Cell19
  | ⟨20,_⟩ => exact repair12241Cell20
  | ⟨21,_⟩ => exact repair12241Cell21
  | ⟨22,_⟩ => exact repair12241Cell22
  | ⟨23,_⟩ => exact repair12241Cell23
  | ⟨24,_⟩ => exact repair12241Cell24
  | ⟨25,_⟩ => exact repair12241Cell25
  | ⟨26,_⟩ => exact repair12241Cell26
  | ⟨27,_⟩ => exact repair12241Cell27
  | ⟨28,_⟩ => exact repair12241Cell28
  | ⟨29,_⟩ => exact repair12241Cell29
  | ⟨30,_⟩ => exact repair12241Cell30
  | ⟨31,_⟩ => exact repair12241Cell31
  | ⟨32,_⟩ => exact repair12241Cell32
  | ⟨33,_⟩ => exact repair12241Cell33
  | ⟨34,_⟩ => exact repair12241Cell34
  | ⟨35,_⟩ => exact repair12241Cell35
  | ⟨36,_⟩ => exact repair12241Cell36
  | ⟨37,_⟩ => exact repair12241Cell37
  | ⟨38,_⟩ => exact repair12241Cell38
  | ⟨39,_⟩ => exact repair12241Cell39
  | ⟨40,_⟩ => exact repair12241Cell40
  | ⟨41,_⟩ => exact repair12241Cell41
  | ⟨42,_⟩ => exact repair12241Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12241 : FrameRepair 12241 scalarRow12241 where
  cap := cap12241
  cap_nonneg := fun j => (repair12241Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12241])
  endpoint := fun j => (repair12241Cells j).2.1
  endpoint_upper := fun j => (repair12241Cells j).2.2.1
  frame := fun j => (repair12241Cells j).2.2.2

noncomputable def cap12242 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975721 / 500000000 : ℝ)
  | ⟨1,_⟩ => (69088651 / 250000000 : ℝ)
  | ⟨2,_⟩ => (27675677 / 100000000 : ℝ)
  | ⟨3,_⟩ => (138578969 / 500000000 : ℝ)
  | ⟨4,_⟩ => (55511623 / 200000000 : ℝ)
  | ⟨5,_⟩ => (138978651 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278355027 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (55750449 / 200000000 : ℝ)
  | ⟨8,_⟩ => (279148487 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69885939 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279938053 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280330901 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280723271 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140557097 / 500000000 : ℝ)
  | ⟨14,_⟩ => (35188131 / 125000000 : ℝ)
  | ⟨15,_⟩ => (140947401 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282283613 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (70667873 / 250000000 : ℝ)
  | ⟨18,_⟩ => (283058431 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (7086111 / 25000000 : ℝ)
  | ⟨20,_⟩ => (141914761 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284213687 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284596927 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (71244689 / 250000000 : ℝ)
  | ⟨24,_⟩ => (71340043 / 250000000 : ℝ)
  | ⟨25,_⟩ => (142870113 / 500000000 : ℝ)
  | ⟨26,_⟩ => (143059937 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286498123 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143437737 / 500000000 : ℝ)
  | ⟨29,_⟩ => (28725193 / 100000000 : ℝ)
  | ⟨30,_⟩ => (287626991 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (288001667 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288375461 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (57749573 / 200000000 : ℝ)
  | ⟨34,_⟩ => (289119393 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (2261641 / 7812500 : ℝ)
  | ⟨36,_⟩ => (289859827 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (58045749 / 200000000 : ℝ)
  | ⟨38,_⟩ => (145298399 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290963477 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291329297 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (58338853 / 200000000 : ℝ)
  | ⟨42,_⟩ => (14602919 / 50000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12242Cell0 :
    0 ≤ cap12242 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨0,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12242 ⟨0,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨0,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell1 :
    0 ≤ cap12242 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨1,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12242 ⟨1,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨1,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell2 :
    0 ≤ cap12242 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨2,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12242 ⟨2,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨2,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell3 :
    0 ≤ cap12242 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨3,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12242 ⟨3,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨3,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell4 :
    0 ≤ cap12242 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨4,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12242 ⟨4,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨4,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell5 :
    0 ≤ cap12242 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨5,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12242 ⟨5,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨5,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell6 :
    0 ≤ cap12242 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨6,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12242 ⟨6,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨6,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell7 :
    0 ≤ cap12242 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨7,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12242 ⟨7,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨7,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell8 :
    0 ≤ cap12242 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨8,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12242 ⟨8,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨8,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell9 :
    0 ≤ cap12242 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨9,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12242 ⟨9,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨9,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell10 :
    0 ≤ cap12242 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨10,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12242 ⟨10,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨10,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell11 :
    0 ≤ cap12242 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨11,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12242 ⟨11,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨11,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell12 :
    0 ≤ cap12242 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨12,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12242 ⟨12,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨12,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell13 :
    0 ≤ cap12242 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨13,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12242 ⟨13,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨13,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell14 :
    0 ≤ cap12242 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨14,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12242 ⟨14,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨14,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell15 :
    0 ≤ cap12242 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨15,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12242 ⟨15,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨15,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell16 :
    0 ≤ cap12242 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨16,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12242 ⟨16,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨16,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell17 :
    0 ≤ cap12242 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨17,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12242 ⟨17,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨17,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell18 :
    0 ≤ cap12242 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨18,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12242 ⟨18,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨18,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell19 :
    0 ≤ cap12242 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨19,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12242 ⟨19,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨19,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell20 :
    0 ≤ cap12242 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨20,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12242 ⟨20,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨20,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell21 :
    0 ≤ cap12242 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨21,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12242 ⟨21,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨21,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell22 :
    0 ≤ cap12242 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨22,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12242 ⟨22,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨22,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell23 :
    0 ≤ cap12242 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨23,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12242 ⟨23,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨23,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell24 :
    0 ≤ cap12242 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨24,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12242 ⟨24,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨24,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell25 :
    0 ≤ cap12242 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨25,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12242 ⟨25,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨25,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell26 :
    0 ≤ cap12242 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨26,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12242 ⟨26,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨26,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell27 :
    0 ≤ cap12242 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨27,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12242 ⟨27,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨27,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell28 :
    0 ≤ cap12242 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨28,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12242 ⟨28,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨28,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell29 :
    0 ≤ cap12242 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨29,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12242 ⟨29,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨29,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell30 :
    0 ≤ cap12242 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨30,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12242 ⟨30,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨30,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell31 :
    0 ≤ cap12242 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨31,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12242 ⟨31,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨31,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell32 :
    0 ≤ cap12242 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨32,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12242 ⟨32,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨32,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell33 :
    0 ≤ cap12242 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨33,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12242 ⟨33,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨33,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell34 :
    0 ≤ cap12242 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨34,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12242 ⟨34,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨34,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell35 :
    0 ≤ cap12242 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨35,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12242 ⟨35,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨35,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell36 :
    0 ≤ cap12242 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨36,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12242 ⟨36,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨36,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell37 :
    0 ≤ cap12242 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨37,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12242 ⟨37,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨37,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell38 :
    0 ≤ cap12242 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨38,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12242 ⟨38,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨38,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell39 :
    0 ≤ cap12242 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨39,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12242 ⟨39,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨39,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell40 :
    0 ≤ cap12242 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨40,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12242 ⟨40,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨40,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell41 :
    0 ≤ cap12242 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨41,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12242 ⟨41,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨41,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cell42 :
    0 ≤ cap12242 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12242 (parameters ⟨42,by decide⟩)
      (scalarRow12242.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12242 ⟨42,by decide⟩ ∧
    (scalarRow12242.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 ⟨42,by decide⟩ + (scalarRow12242.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12242.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12242.targetFrame := by
  norm_num [cap12242, scalarRow12242, sourceIndex, cell12242, BstLean.Part263.envelope, parameters]

theorem repair12242Cells (j : Fin 43) :
    0 ≤ cap12242 j ∧
    BstLean.Part263.envelope 12242 (parameters j) (scalarRow12242.table (sourceIndex j)).upper ≤ cap12242 j ∧
    (scalarRow12242.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12242 j + (scalarRow12242.table (sourceIndex j)).centre) /
      (scalarRow12242.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12242.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12242Cell0
  | ⟨1,_⟩ => exact repair12242Cell1
  | ⟨2,_⟩ => exact repair12242Cell2
  | ⟨3,_⟩ => exact repair12242Cell3
  | ⟨4,_⟩ => exact repair12242Cell4
  | ⟨5,_⟩ => exact repair12242Cell5
  | ⟨6,_⟩ => exact repair12242Cell6
  | ⟨7,_⟩ => exact repair12242Cell7
  | ⟨8,_⟩ => exact repair12242Cell8
  | ⟨9,_⟩ => exact repair12242Cell9
  | ⟨10,_⟩ => exact repair12242Cell10
  | ⟨11,_⟩ => exact repair12242Cell11
  | ⟨12,_⟩ => exact repair12242Cell12
  | ⟨13,_⟩ => exact repair12242Cell13
  | ⟨14,_⟩ => exact repair12242Cell14
  | ⟨15,_⟩ => exact repair12242Cell15
  | ⟨16,_⟩ => exact repair12242Cell16
  | ⟨17,_⟩ => exact repair12242Cell17
  | ⟨18,_⟩ => exact repair12242Cell18
  | ⟨19,_⟩ => exact repair12242Cell19
  | ⟨20,_⟩ => exact repair12242Cell20
  | ⟨21,_⟩ => exact repair12242Cell21
  | ⟨22,_⟩ => exact repair12242Cell22
  | ⟨23,_⟩ => exact repair12242Cell23
  | ⟨24,_⟩ => exact repair12242Cell24
  | ⟨25,_⟩ => exact repair12242Cell25
  | ⟨26,_⟩ => exact repair12242Cell26
  | ⟨27,_⟩ => exact repair12242Cell27
  | ⟨28,_⟩ => exact repair12242Cell28
  | ⟨29,_⟩ => exact repair12242Cell29
  | ⟨30,_⟩ => exact repair12242Cell30
  | ⟨31,_⟩ => exact repair12242Cell31
  | ⟨32,_⟩ => exact repair12242Cell32
  | ⟨33,_⟩ => exact repair12242Cell33
  | ⟨34,_⟩ => exact repair12242Cell34
  | ⟨35,_⟩ => exact repair12242Cell35
  | ⟨36,_⟩ => exact repair12242Cell36
  | ⟨37,_⟩ => exact repair12242Cell37
  | ⟨38,_⟩ => exact repair12242Cell38
  | ⟨39,_⟩ => exact repair12242Cell39
  | ⟨40,_⟩ => exact repair12242Cell40
  | ⟨41,_⟩ => exact repair12242Cell41
  | ⟨42,_⟩ => exact repair12242Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12242 : FrameRepair 12242 scalarRow12242 where
  cap := cap12242
  cap_nonneg := fun j => (repair12242Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12242])
  endpoint := fun j => (repair12242Cells j).2.1
  endpoint_upper := fun j => (repair12242Cells j).2.2.1
  frame := fun j => (repair12242Cells j).2.2.2

noncomputable def cap12243 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975683 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276354521 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276756681 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277157843 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277558013 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277957193 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (8698591 / 31250000 : ℝ)
  | ⟨7,_⟩ => (69688031 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279148359 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139771811 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279937913 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140165377 / 500000000 : ℝ)
  | ⟨12,_⟩ => (140361559 / 500000000 : ℝ)
  | ⟨13,_⟩ => (140557017 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140752441 / 500000000 : ℝ)
  | ⟨15,_⟩ => (28189463 / 100000000 : ℝ)
  | ⟨16,_⟩ => (56456687 / 200000000 : ℝ)
  | ⟨17,_⟩ => (282671307 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (884557 / 3125000 : ℝ)
  | ⟨19,_⟩ => (283444243 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283829319 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284213477 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284596711 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142489267 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285359943 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285739991 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286119633 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71624469 / 250000000 : ℝ)
  | ⟨28,_⟩ => (286875221 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (28725167 / 100000000 : ℝ)
  | ⟨30,_⟩ => (11505069 / 40000000 : ℝ)
  | ⟨31,_⟩ => (57600279 / 200000000 : ℝ)
  | ⟨32,_⟩ => (18023449 / 62500000 : ℝ)
  | ⟨33,_⟩ => (288747581 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289119103 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289489753 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (11594381 / 40000000 : ℝ)
  | ⟨37,_⟩ => (290228437 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (72649121 / 250000000 : ℝ)
  | ⟨39,_⟩ => (290963157 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291328971 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291693933 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146029021 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12243Cell0 :
    0 ≤ cap12243 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨0,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12243 ⟨0,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨0,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell1 :
    0 ≤ cap12243 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨1,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12243 ⟨1,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨1,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell2 :
    0 ≤ cap12243 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨2,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12243 ⟨2,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨2,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell3 :
    0 ≤ cap12243 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨3,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12243 ⟨3,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨3,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell4 :
    0 ≤ cap12243 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨4,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12243 ⟨4,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨4,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell5 :
    0 ≤ cap12243 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨5,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12243 ⟨5,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨5,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell6 :
    0 ≤ cap12243 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨6,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12243 ⟨6,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨6,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell7 :
    0 ≤ cap12243 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨7,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12243 ⟨7,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨7,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell8 :
    0 ≤ cap12243 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨8,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12243 ⟨8,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨8,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell9 :
    0 ≤ cap12243 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨9,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12243 ⟨9,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨9,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell10 :
    0 ≤ cap12243 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨10,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12243 ⟨10,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨10,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell11 :
    0 ≤ cap12243 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨11,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12243 ⟨11,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨11,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell12 :
    0 ≤ cap12243 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨12,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12243 ⟨12,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨12,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell13 :
    0 ≤ cap12243 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨13,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12243 ⟨13,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨13,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell14 :
    0 ≤ cap12243 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨14,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12243 ⟨14,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨14,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell15 :
    0 ≤ cap12243 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨15,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12243 ⟨15,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨15,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell16 :
    0 ≤ cap12243 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨16,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12243 ⟨16,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨16,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell17 :
    0 ≤ cap12243 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨17,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12243 ⟨17,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨17,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell18 :
    0 ≤ cap12243 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨18,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12243 ⟨18,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨18,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell19 :
    0 ≤ cap12243 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨19,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12243 ⟨19,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨19,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell20 :
    0 ≤ cap12243 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨20,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12243 ⟨20,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨20,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell21 :
    0 ≤ cap12243 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨21,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12243 ⟨21,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨21,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell22 :
    0 ≤ cap12243 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨22,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12243 ⟨22,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨22,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell23 :
    0 ≤ cap12243 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨23,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12243 ⟨23,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨23,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell24 :
    0 ≤ cap12243 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨24,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12243 ⟨24,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨24,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell25 :
    0 ≤ cap12243 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨25,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12243 ⟨25,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨25,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell26 :
    0 ≤ cap12243 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨26,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12243 ⟨26,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨26,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell27 :
    0 ≤ cap12243 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨27,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12243 ⟨27,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨27,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell28 :
    0 ≤ cap12243 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨28,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12243 ⟨28,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨28,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell29 :
    0 ≤ cap12243 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨29,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12243 ⟨29,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨29,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell30 :
    0 ≤ cap12243 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨30,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12243 ⟨30,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨30,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell31 :
    0 ≤ cap12243 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨31,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12243 ⟨31,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨31,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell32 :
    0 ≤ cap12243 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨32,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12243 ⟨32,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨32,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell33 :
    0 ≤ cap12243 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨33,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12243 ⟨33,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨33,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell34 :
    0 ≤ cap12243 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨34,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12243 ⟨34,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨34,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell35 :
    0 ≤ cap12243 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨35,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12243 ⟨35,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨35,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell36 :
    0 ≤ cap12243 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨36,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12243 ⟨36,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨36,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell37 :
    0 ≤ cap12243 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨37,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12243 ⟨37,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨37,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell38 :
    0 ≤ cap12243 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨38,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12243 ⟨38,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨38,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell39 :
    0 ≤ cap12243 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨39,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12243 ⟨39,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨39,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell40 :
    0 ≤ cap12243 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨40,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12243 ⟨40,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨40,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell41 :
    0 ≤ cap12243 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨41,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12243 ⟨41,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨41,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cell42 :
    0 ≤ cap12243 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12243 (parameters ⟨42,by decide⟩)
      (scalarRow12243.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12243 ⟨42,by decide⟩ ∧
    (scalarRow12243.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 ⟨42,by decide⟩ + (scalarRow12243.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12243.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12243.targetFrame := by
  norm_num [cap12243, scalarRow12243, sourceIndex, cell12243, BstLean.Part263.envelope, parameters]

theorem repair12243Cells (j : Fin 43) :
    0 ≤ cap12243 j ∧
    BstLean.Part263.envelope 12243 (parameters j) (scalarRow12243.table (sourceIndex j)).upper ≤ cap12243 j ∧
    (scalarRow12243.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12243 j + (scalarRow12243.table (sourceIndex j)).centre) /
      (scalarRow12243.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12243.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12243Cell0
  | ⟨1,_⟩ => exact repair12243Cell1
  | ⟨2,_⟩ => exact repair12243Cell2
  | ⟨3,_⟩ => exact repair12243Cell3
  | ⟨4,_⟩ => exact repair12243Cell4
  | ⟨5,_⟩ => exact repair12243Cell5
  | ⟨6,_⟩ => exact repair12243Cell6
  | ⟨7,_⟩ => exact repair12243Cell7
  | ⟨8,_⟩ => exact repair12243Cell8
  | ⟨9,_⟩ => exact repair12243Cell9
  | ⟨10,_⟩ => exact repair12243Cell10
  | ⟨11,_⟩ => exact repair12243Cell11
  | ⟨12,_⟩ => exact repair12243Cell12
  | ⟨13,_⟩ => exact repair12243Cell13
  | ⟨14,_⟩ => exact repair12243Cell14
  | ⟨15,_⟩ => exact repair12243Cell15
  | ⟨16,_⟩ => exact repair12243Cell16
  | ⟨17,_⟩ => exact repair12243Cell17
  | ⟨18,_⟩ => exact repair12243Cell18
  | ⟨19,_⟩ => exact repair12243Cell19
  | ⟨20,_⟩ => exact repair12243Cell20
  | ⟨21,_⟩ => exact repair12243Cell21
  | ⟨22,_⟩ => exact repair12243Cell22
  | ⟨23,_⟩ => exact repair12243Cell23
  | ⟨24,_⟩ => exact repair12243Cell24
  | ⟨25,_⟩ => exact repair12243Cell25
  | ⟨26,_⟩ => exact repair12243Cell26
  | ⟨27,_⟩ => exact repair12243Cell27
  | ⟨28,_⟩ => exact repair12243Cell28
  | ⟨29,_⟩ => exact repair12243Cell29
  | ⟨30,_⟩ => exact repair12243Cell30
  | ⟨31,_⟩ => exact repair12243Cell31
  | ⟨32,_⟩ => exact repair12243Cell32
  | ⟨33,_⟩ => exact repair12243Cell33
  | ⟨34,_⟩ => exact repair12243Cell34
  | ⟨35,_⟩ => exact repair12243Cell35
  | ⟨36,_⟩ => exact repair12243Cell36
  | ⟨37,_⟩ => exact repair12243Cell37
  | ⟨38,_⟩ => exact repair12243Cell38
  | ⟨39,_⟩ => exact repair12243Cell39
  | ⟨40,_⟩ => exact repair12243Cell40
  | ⟨41,_⟩ => exact repair12243Cell41
  | ⟨42,_⟩ => exact repair12243Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12243 : FrameRepair 12243 scalarRow12243 where
  cap := cap12243
  cap_nonneg := fun j => (repair12243Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12243])
  endpoint := fun j => (repair12243Cells j).2.1
  endpoint_upper := fun j => (repair12243Cells j).2.2.1
  frame := fun j => (repair12243Cells j).2.2.2

noncomputable def cap12244 : Fin 43 → ℝ
  | ⟨0,_⟩ => (27595129 / 100000000 : ℝ)
  | ⟨1,_⟩ => (276354439 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (17297287 / 62500000 : ℝ)
  | ⟨3,_⟩ => (277157747 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277557911 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (55591417 / 200000000 : ℝ)
  | ⟨6,_⟩ => (278354797 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278752003 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (34893529 / 125000000 : ℝ)
  | ⟨9,_⟩ => (4367867 / 15625000 : ℝ)
  | ⟨10,_⟩ => (69984443 / 250000000 : ℝ)
  | ⟨11,_⟩ => (17520663 / 62500000 : ℝ)
  | ⟨12,_⟩ => (56144593 / 200000000 : ℝ)
  | ⟨13,_⟩ => (2248911 / 8000000 : ℝ)
  | ⟨14,_⟩ => (70376179 / 250000000 : ℝ)
  | ⟨15,_⟩ => (140947229 / 500000000 : ℝ)
  | ⟨16,_⟩ => (35285407 / 125000000 : ℝ)
  | ⟨17,_⟩ => (141335561 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283058049 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141722023 / 500000000 : ℝ)
  | ⟨20,_⟩ => (56765823 / 200000000 : ℝ)
  | ⟨21,_⟩ => (284213267 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (56919299 / 200000000 : ℝ)
  | ⟨23,_⟩ => (35622289 / 125000000 : ℝ)
  | ⟨24,_⟩ => (57071943 / 200000000 : ℝ)
  | ⟨25,_⟩ => (71434939 / 250000000 : ℝ)
  | ⟨26,_⟩ => (286119393 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286497629 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (35859371 / 125000000 : ℝ)
  | ⟨29,_⟩ => (287251411 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (14381323 / 50000000 : ℝ)
  | ⟨31,_⟩ => (72000281 / 250000000 : ℝ)
  | ⟨32,_⟩ => (144187453 / 500000000 : ℝ)
  | ⟨33,_⟩ => (144373649 / 500000000 : ℝ)
  | ⟨34,_⟩ => (289118813 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289489457 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289859223 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290228129 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (29059617 / 100000000 : ℝ)
  | ⟨39,_⟩ => (290962837 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58265729 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291693601 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (36507213 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12244Cell0 :
    0 ≤ cap12244 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨0,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12244 ⟨0,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨0,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell1 :
    0 ≤ cap12244 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨1,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12244 ⟨1,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨1,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell2 :
    0 ≤ cap12244 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨2,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12244 ⟨2,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨2,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell3 :
    0 ≤ cap12244 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨3,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12244 ⟨3,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨3,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell4 :
    0 ≤ cap12244 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨4,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12244 ⟨4,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨4,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell5 :
    0 ≤ cap12244 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨5,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12244 ⟨5,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨5,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell6 :
    0 ≤ cap12244 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨6,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12244 ⟨6,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨6,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell7 :
    0 ≤ cap12244 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨7,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12244 ⟨7,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨7,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell8 :
    0 ≤ cap12244 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨8,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12244 ⟨8,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨8,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell9 :
    0 ≤ cap12244 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨9,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12244 ⟨9,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨9,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell10 :
    0 ≤ cap12244 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨10,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12244 ⟨10,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨10,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell11 :
    0 ≤ cap12244 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨11,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12244 ⟨11,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨11,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell12 :
    0 ≤ cap12244 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨12,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12244 ⟨12,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨12,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell13 :
    0 ≤ cap12244 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨13,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12244 ⟨13,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨13,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell14 :
    0 ≤ cap12244 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨14,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12244 ⟨14,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨14,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell15 :
    0 ≤ cap12244 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨15,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12244 ⟨15,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨15,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell16 :
    0 ≤ cap12244 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨16,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12244 ⟨16,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨16,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell17 :
    0 ≤ cap12244 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨17,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12244 ⟨17,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨17,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell18 :
    0 ≤ cap12244 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨18,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12244 ⟨18,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨18,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell19 :
    0 ≤ cap12244 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨19,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12244 ⟨19,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨19,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell20 :
    0 ≤ cap12244 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨20,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12244 ⟨20,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨20,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell21 :
    0 ≤ cap12244 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨21,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12244 ⟨21,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨21,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell22 :
    0 ≤ cap12244 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨22,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12244 ⟨22,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨22,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell23 :
    0 ≤ cap12244 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨23,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12244 ⟨23,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨23,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell24 :
    0 ≤ cap12244 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨24,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12244 ⟨24,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨24,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell25 :
    0 ≤ cap12244 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨25,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12244 ⟨25,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨25,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell26 :
    0 ≤ cap12244 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨26,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12244 ⟨26,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨26,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell27 :
    0 ≤ cap12244 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨27,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12244 ⟨27,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨27,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell28 :
    0 ≤ cap12244 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨28,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12244 ⟨28,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨28,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell29 :
    0 ≤ cap12244 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨29,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12244 ⟨29,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨29,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell30 :
    0 ≤ cap12244 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨30,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12244 ⟨30,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨30,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell31 :
    0 ≤ cap12244 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨31,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12244 ⟨31,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨31,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell32 :
    0 ≤ cap12244 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨32,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12244 ⟨32,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨32,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell33 :
    0 ≤ cap12244 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨33,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12244 ⟨33,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨33,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell34 :
    0 ≤ cap12244 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨34,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12244 ⟨34,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨34,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell35 :
    0 ≤ cap12244 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨35,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12244 ⟨35,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨35,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell36 :
    0 ≤ cap12244 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨36,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12244 ⟨36,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨36,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell37 :
    0 ≤ cap12244 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨37,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12244 ⟨37,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨37,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell38 :
    0 ≤ cap12244 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨38,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12244 ⟨38,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨38,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell39 :
    0 ≤ cap12244 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨39,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12244 ⟨39,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨39,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell40 :
    0 ≤ cap12244 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨40,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12244 ⟨40,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨40,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell41 :
    0 ≤ cap12244 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨41,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12244 ⟨41,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨41,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cell42 :
    0 ≤ cap12244 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12244 (parameters ⟨42,by decide⟩)
      (scalarRow12244.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12244 ⟨42,by decide⟩ ∧
    (scalarRow12244.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 ⟨42,by decide⟩ + (scalarRow12244.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12244.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12244.targetFrame := by
  norm_num [cap12244, scalarRow12244, sourceIndex, cell12244, BstLean.Part263.envelope, parameters]

theorem repair12244Cells (j : Fin 43) :
    0 ≤ cap12244 j ∧
    BstLean.Part263.envelope 12244 (parameters j) (scalarRow12244.table (sourceIndex j)).upper ≤ cap12244 j ∧
    (scalarRow12244.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12244 j + (scalarRow12244.table (sourceIndex j)).centre) /
      (scalarRow12244.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12244.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12244Cell0
  | ⟨1,_⟩ => exact repair12244Cell1
  | ⟨2,_⟩ => exact repair12244Cell2
  | ⟨3,_⟩ => exact repair12244Cell3
  | ⟨4,_⟩ => exact repair12244Cell4
  | ⟨5,_⟩ => exact repair12244Cell5
  | ⟨6,_⟩ => exact repair12244Cell6
  | ⟨7,_⟩ => exact repair12244Cell7
  | ⟨8,_⟩ => exact repair12244Cell8
  | ⟨9,_⟩ => exact repair12244Cell9
  | ⟨10,_⟩ => exact repair12244Cell10
  | ⟨11,_⟩ => exact repair12244Cell11
  | ⟨12,_⟩ => exact repair12244Cell12
  | ⟨13,_⟩ => exact repair12244Cell13
  | ⟨14,_⟩ => exact repair12244Cell14
  | ⟨15,_⟩ => exact repair12244Cell15
  | ⟨16,_⟩ => exact repair12244Cell16
  | ⟨17,_⟩ => exact repair12244Cell17
  | ⟨18,_⟩ => exact repair12244Cell18
  | ⟨19,_⟩ => exact repair12244Cell19
  | ⟨20,_⟩ => exact repair12244Cell20
  | ⟨21,_⟩ => exact repair12244Cell21
  | ⟨22,_⟩ => exact repair12244Cell22
  | ⟨23,_⟩ => exact repair12244Cell23
  | ⟨24,_⟩ => exact repair12244Cell24
  | ⟨25,_⟩ => exact repair12244Cell25
  | ⟨26,_⟩ => exact repair12244Cell26
  | ⟨27,_⟩ => exact repair12244Cell27
  | ⟨28,_⟩ => exact repair12244Cell28
  | ⟨29,_⟩ => exact repair12244Cell29
  | ⟨30,_⟩ => exact repair12244Cell30
  | ⟨31,_⟩ => exact repair12244Cell31
  | ⟨32,_⟩ => exact repair12244Cell32
  | ⟨33,_⟩ => exact repair12244Cell33
  | ⟨34,_⟩ => exact repair12244Cell34
  | ⟨35,_⟩ => exact repair12244Cell35
  | ⟨36,_⟩ => exact repair12244Cell36
  | ⟨37,_⟩ => exact repair12244Cell37
  | ⟨38,_⟩ => exact repair12244Cell38
  | ⟨39,_⟩ => exact repair12244Cell39
  | ⟨40,_⟩ => exact repair12244Cell40
  | ⟨41,_⟩ => exact repair12244Cell41
  | ⟨42,_⟩ => exact repair12244Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12244 : FrameRepair 12244 scalarRow12244 where
  cap := cap12244
  cap_nonneg := fun j => (repair12244Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12244])
  endpoint := fun j => (repair12244Cells j).2.1
  endpoint_upper := fun j => (repair12244Cells j).2.2.1
  frame := fun j => (repair12244Cells j).2.2.2

noncomputable def cap12245 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55190243 / 200000000 : ℝ)
  | ⟨1,_⟩ => (69088589 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276756503 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (69289413 / 250000000 : ℝ)
  | ⟨4,_⟩ => (27755781 / 100000000 : ℝ)
  | ⟨5,_⟩ => (277956977 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278354683 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139375941 / 500000000 : ℝ)
  | ⟨8,_⟩ => (34893513 / 125000000 : ℝ)
  | ⟨9,_⟩ => (139771677 / 500000000 : ℝ)
  | ⟨10,_⟩ => (8748051 / 31250000 : ℝ)
  | ⟨11,_⟩ => (280330461 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (70180703 / 250000000 : ℝ)
  | ⟨13,_⟩ => (56222743 / 200000000 : ℝ)
  | ⟨14,_⟩ => (281504551 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140947143 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141141539 / 500000000 : ℝ)
  | ⟨17,_⟩ => (141335469 / 500000000 : ℝ)
  | ⟨18,_⟩ => (141528929 / 500000000 : ℝ)
  | ⟨19,_⟩ => (35430481 / 125000000 : ℝ)
  | ⟨20,_⟩ => (17739307 / 62500000 : ℝ)
  | ⟨21,_⟩ => (142106529 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284596279 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284978089 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142679743 / 500000000 : ℝ)
  | ⟨25,_⟩ => (142869761 / 500000000 : ℝ)
  | ⟨26,_⟩ => (17882447 / 62500000 : ℝ)
  | ⟨27,_⟩ => (143248691 / 500000000 : ℝ)
  | ⟨28,_⟩ => (57374943 / 200000000 : ℝ)
  | ⟨29,_⟩ => (17953197 / 62500000 : ℝ)
  | ⟨30,_⟩ => (57525239 / 200000000 : ℝ)
  | ⟨31,_⟩ => (72000213 / 250000000 : ℝ)
  | ⟨32,_⟩ => (72093657 / 250000000 : ℝ)
  | ⟨33,_⟩ => (144373507 / 500000000 : ℝ)
  | ⟨34,_⟩ => (72279631 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289489161 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289858921 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290227821 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (18162241 / 62500000 : ℝ)
  | ⟨39,_⟩ => (290962517 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291328319 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291693269 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292057367 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12245Cell0 :
    0 ≤ cap12245 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨0,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12245 ⟨0,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨0,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell1 :
    0 ≤ cap12245 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨1,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12245 ⟨1,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨1,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell2 :
    0 ≤ cap12245 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨2,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12245 ⟨2,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨2,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell3 :
    0 ≤ cap12245 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨3,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12245 ⟨3,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨3,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell4 :
    0 ≤ cap12245 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨4,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12245 ⟨4,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨4,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell5 :
    0 ≤ cap12245 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨5,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12245 ⟨5,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨5,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell6 :
    0 ≤ cap12245 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨6,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12245 ⟨6,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨6,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell7 :
    0 ≤ cap12245 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨7,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12245 ⟨7,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨7,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell8 :
    0 ≤ cap12245 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨8,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12245 ⟨8,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨8,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell9 :
    0 ≤ cap12245 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨9,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12245 ⟨9,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨9,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell10 :
    0 ≤ cap12245 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨10,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12245 ⟨10,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨10,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell11 :
    0 ≤ cap12245 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨11,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12245 ⟨11,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨11,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell12 :
    0 ≤ cap12245 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨12,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12245 ⟨12,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨12,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell13 :
    0 ≤ cap12245 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨13,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12245 ⟨13,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨13,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell14 :
    0 ≤ cap12245 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨14,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12245 ⟨14,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨14,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell15 :
    0 ≤ cap12245 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨15,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12245 ⟨15,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨15,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell16 :
    0 ≤ cap12245 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨16,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12245 ⟨16,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨16,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell17 :
    0 ≤ cap12245 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨17,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12245 ⟨17,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨17,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell18 :
    0 ≤ cap12245 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨18,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12245 ⟨18,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨18,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell19 :
    0 ≤ cap12245 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨19,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12245 ⟨19,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨19,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell20 :
    0 ≤ cap12245 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨20,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12245 ⟨20,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨20,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell21 :
    0 ≤ cap12245 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨21,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12245 ⟨21,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨21,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell22 :
    0 ≤ cap12245 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨22,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12245 ⟨22,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨22,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell23 :
    0 ≤ cap12245 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨23,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12245 ⟨23,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨23,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell24 :
    0 ≤ cap12245 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨24,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12245 ⟨24,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨24,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell25 :
    0 ≤ cap12245 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨25,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12245 ⟨25,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨25,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell26 :
    0 ≤ cap12245 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨26,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12245 ⟨26,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨26,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell27 :
    0 ≤ cap12245 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨27,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12245 ⟨27,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨27,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell28 :
    0 ≤ cap12245 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨28,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12245 ⟨28,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨28,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell29 :
    0 ≤ cap12245 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨29,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12245 ⟨29,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨29,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell30 :
    0 ≤ cap12245 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨30,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12245 ⟨30,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨30,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell31 :
    0 ≤ cap12245 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨31,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12245 ⟨31,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨31,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell32 :
    0 ≤ cap12245 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨32,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12245 ⟨32,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨32,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell33 :
    0 ≤ cap12245 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨33,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12245 ⟨33,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨33,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell34 :
    0 ≤ cap12245 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨34,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12245 ⟨34,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨34,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell35 :
    0 ≤ cap12245 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨35,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12245 ⟨35,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨35,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell36 :
    0 ≤ cap12245 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨36,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12245 ⟨36,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨36,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell37 :
    0 ≤ cap12245 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨37,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12245 ⟨37,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨37,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell38 :
    0 ≤ cap12245 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨38,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12245 ⟨38,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨38,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell39 :
    0 ≤ cap12245 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨39,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12245 ⟨39,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨39,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell40 :
    0 ≤ cap12245 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨40,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12245 ⟨40,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨40,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell41 :
    0 ≤ cap12245 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨41,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12245 ⟨41,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨41,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cell42 :
    0 ≤ cap12245 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12245 (parameters ⟨42,by decide⟩)
      (scalarRow12245.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12245 ⟨42,by decide⟩ ∧
    (scalarRow12245.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 ⟨42,by decide⟩ + (scalarRow12245.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12245.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12245.targetFrame := by
  norm_num [cap12245, scalarRow12245, sourceIndex, cell12245, BstLean.Part263.envelope, parameters]

theorem repair12245Cells (j : Fin 43) :
    0 ≤ cap12245 j ∧
    BstLean.Part263.envelope 12245 (parameters j) (scalarRow12245.table (sourceIndex j)).upper ≤ cap12245 j ∧
    (scalarRow12245.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12245 j + (scalarRow12245.table (sourceIndex j)).centre) /
      (scalarRow12245.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12245.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12245Cell0
  | ⟨1,_⟩ => exact repair12245Cell1
  | ⟨2,_⟩ => exact repair12245Cell2
  | ⟨3,_⟩ => exact repair12245Cell3
  | ⟨4,_⟩ => exact repair12245Cell4
  | ⟨5,_⟩ => exact repair12245Cell5
  | ⟨6,_⟩ => exact repair12245Cell6
  | ⟨7,_⟩ => exact repair12245Cell7
  | ⟨8,_⟩ => exact repair12245Cell8
  | ⟨9,_⟩ => exact repair12245Cell9
  | ⟨10,_⟩ => exact repair12245Cell10
  | ⟨11,_⟩ => exact repair12245Cell11
  | ⟨12,_⟩ => exact repair12245Cell12
  | ⟨13,_⟩ => exact repair12245Cell13
  | ⟨14,_⟩ => exact repair12245Cell14
  | ⟨15,_⟩ => exact repair12245Cell15
  | ⟨16,_⟩ => exact repair12245Cell16
  | ⟨17,_⟩ => exact repair12245Cell17
  | ⟨18,_⟩ => exact repair12245Cell18
  | ⟨19,_⟩ => exact repair12245Cell19
  | ⟨20,_⟩ => exact repair12245Cell20
  | ⟨21,_⟩ => exact repair12245Cell21
  | ⟨22,_⟩ => exact repair12245Cell22
  | ⟨23,_⟩ => exact repair12245Cell23
  | ⟨24,_⟩ => exact repair12245Cell24
  | ⟨25,_⟩ => exact repair12245Cell25
  | ⟨26,_⟩ => exact repair12245Cell26
  | ⟨27,_⟩ => exact repair12245Cell27
  | ⟨28,_⟩ => exact repair12245Cell28
  | ⟨29,_⟩ => exact repair12245Cell29
  | ⟨30,_⟩ => exact repair12245Cell30
  | ⟨31,_⟩ => exact repair12245Cell31
  | ⟨32,_⟩ => exact repair12245Cell32
  | ⟨33,_⟩ => exact repair12245Cell33
  | ⟨34,_⟩ => exact repair12245Cell34
  | ⟨35,_⟩ => exact repair12245Cell35
  | ⟨36,_⟩ => exact repair12245Cell36
  | ⟨37,_⟩ => exact repair12245Cell37
  | ⟨38,_⟩ => exact repair12245Cell38
  | ⟨39,_⟩ => exact repair12245Cell39
  | ⟨40,_⟩ => exact repair12245Cell40
  | ⟨41,_⟩ => exact repair12245Cell41
  | ⟨42,_⟩ => exact repair12245Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12245 : FrameRepair 12245 scalarRow12245 where
  cap := cap12245
  cap_nonneg := fun j => (repair12245Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12245])
  endpoint := fun j => (repair12245Cells j).2.1
  endpoint_upper := fun j => (repair12245Cells j).2.2.1
  frame := fun j => (repair12245Cells j).2.2.2

noncomputable def cap12246 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275951139 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138177137 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138378207 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277157557 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (69389427 / 250000000 : ℝ)
  | ⟨5,_⟩ => (277956869 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (34794321 / 125000000 : ℝ)
  | ⟨7,_⟩ => (3484397 / 12500000 : ℝ)
  | ⟨8,_⟩ => (279147977 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (13977161 / 50000000 : ℝ)
  | ⟨10,_⟩ => (69984373 / 250000000 : ℝ)
  | ⟨11,_⟩ => (140165157 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280722659 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70278389 / 250000000 : ℝ)
  | ⟨14,_⟩ => (56300877 / 200000000 : ℝ)
  | ⟨15,_⟩ => (140947057 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282282899 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282670753 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283057667 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283443651 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (70957177 / 250000000 : ℝ)
  | ⟨21,_⟩ => (17763303 / 62500000 : ℝ)
  | ⟨22,_⟩ => (284596063 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284977867 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142679629 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285739287 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286118911 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (57299427 / 200000000 : ℝ)
  | ⟨28,_⟩ => (143437231 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287250893 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287625929 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (288000581 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288374351 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (28874673 / 100000000 : ℝ)
  | ⟨34,_⟩ => (144559117 / 500000000 : ℝ)
  | ⟨35,_⟩ => (57897773 / 200000000 : ℝ)
  | ⟨36,_⟩ => (289858619 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145113757 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145297771 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290962197 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291327993 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291692937 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292057029 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12246Cell0 :
    0 ≤ cap12246 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨0,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12246 ⟨0,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨0,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell1 :
    0 ≤ cap12246 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨1,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12246 ⟨1,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨1,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell2 :
    0 ≤ cap12246 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨2,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12246 ⟨2,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨2,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell3 :
    0 ≤ cap12246 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨3,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12246 ⟨3,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨3,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell4 :
    0 ≤ cap12246 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨4,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12246 ⟨4,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨4,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell5 :
    0 ≤ cap12246 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨5,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12246 ⟨5,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨5,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell6 :
    0 ≤ cap12246 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨6,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12246 ⟨6,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨6,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell7 :
    0 ≤ cap12246 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨7,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12246 ⟨7,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨7,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell8 :
    0 ≤ cap12246 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨8,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12246 ⟨8,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨8,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell9 :
    0 ≤ cap12246 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨9,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12246 ⟨9,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨9,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell10 :
    0 ≤ cap12246 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨10,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12246 ⟨10,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨10,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell11 :
    0 ≤ cap12246 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨11,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12246 ⟨11,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨11,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell12 :
    0 ≤ cap12246 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨12,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12246 ⟨12,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨12,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell13 :
    0 ≤ cap12246 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨13,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12246 ⟨13,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨13,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell14 :
    0 ≤ cap12246 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨14,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12246 ⟨14,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨14,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell15 :
    0 ≤ cap12246 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨15,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12246 ⟨15,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨15,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell16 :
    0 ≤ cap12246 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨16,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12246 ⟨16,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨16,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell17 :
    0 ≤ cap12246 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨17,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12246 ⟨17,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨17,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell18 :
    0 ≤ cap12246 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨18,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12246 ⟨18,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨18,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell19 :
    0 ≤ cap12246 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨19,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12246 ⟨19,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨19,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell20 :
    0 ≤ cap12246 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨20,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12246 ⟨20,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨20,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell21 :
    0 ≤ cap12246 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨21,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12246 ⟨21,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨21,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell22 :
    0 ≤ cap12246 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨22,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12246 ⟨22,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨22,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell23 :
    0 ≤ cap12246 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨23,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12246 ⟨23,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨23,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell24 :
    0 ≤ cap12246 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨24,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12246 ⟨24,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨24,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell25 :
    0 ≤ cap12246 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨25,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12246 ⟨25,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨25,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell26 :
    0 ≤ cap12246 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨26,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12246 ⟨26,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨26,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell27 :
    0 ≤ cap12246 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨27,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12246 ⟨27,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨27,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell28 :
    0 ≤ cap12246 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨28,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12246 ⟨28,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨28,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell29 :
    0 ≤ cap12246 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨29,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12246 ⟨29,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨29,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell30 :
    0 ≤ cap12246 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨30,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12246 ⟨30,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨30,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell31 :
    0 ≤ cap12246 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨31,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12246 ⟨31,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨31,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell32 :
    0 ≤ cap12246 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨32,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12246 ⟨32,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨32,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell33 :
    0 ≤ cap12246 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨33,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12246 ⟨33,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨33,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell34 :
    0 ≤ cap12246 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨34,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12246 ⟨34,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨34,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell35 :
    0 ≤ cap12246 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨35,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12246 ⟨35,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨35,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell36 :
    0 ≤ cap12246 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨36,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12246 ⟨36,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨36,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell37 :
    0 ≤ cap12246 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨37,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12246 ⟨37,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨37,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell38 :
    0 ≤ cap12246 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨38,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12246 ⟨38,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨38,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell39 :
    0 ≤ cap12246 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨39,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12246 ⟨39,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨39,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell40 :
    0 ≤ cap12246 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨40,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12246 ⟨40,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨40,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell41 :
    0 ≤ cap12246 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨41,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12246 ⟨41,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨41,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cell42 :
    0 ≤ cap12246 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12246 (parameters ⟨42,by decide⟩)
      (scalarRow12246.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12246 ⟨42,by decide⟩ ∧
    (scalarRow12246.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 ⟨42,by decide⟩ + (scalarRow12246.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12246.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12246.targetFrame := by
  norm_num [cap12246, scalarRow12246, sourceIndex, cell12246, BstLean.Part263.envelope, parameters]

theorem repair12246Cells (j : Fin 43) :
    0 ≤ cap12246 j ∧
    BstLean.Part263.envelope 12246 (parameters j) (scalarRow12246.table (sourceIndex j)).upper ≤ cap12246 j ∧
    (scalarRow12246.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12246 j + (scalarRow12246.table (sourceIndex j)).centre) /
      (scalarRow12246.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12246.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12246Cell0
  | ⟨1,_⟩ => exact repair12246Cell1
  | ⟨2,_⟩ => exact repair12246Cell2
  | ⟨3,_⟩ => exact repair12246Cell3
  | ⟨4,_⟩ => exact repair12246Cell4
  | ⟨5,_⟩ => exact repair12246Cell5
  | ⟨6,_⟩ => exact repair12246Cell6
  | ⟨7,_⟩ => exact repair12246Cell7
  | ⟨8,_⟩ => exact repair12246Cell8
  | ⟨9,_⟩ => exact repair12246Cell9
  | ⟨10,_⟩ => exact repair12246Cell10
  | ⟨11,_⟩ => exact repair12246Cell11
  | ⟨12,_⟩ => exact repair12246Cell12
  | ⟨13,_⟩ => exact repair12246Cell13
  | ⟨14,_⟩ => exact repair12246Cell14
  | ⟨15,_⟩ => exact repair12246Cell15
  | ⟨16,_⟩ => exact repair12246Cell16
  | ⟨17,_⟩ => exact repair12246Cell17
  | ⟨18,_⟩ => exact repair12246Cell18
  | ⟨19,_⟩ => exact repair12246Cell19
  | ⟨20,_⟩ => exact repair12246Cell20
  | ⟨21,_⟩ => exact repair12246Cell21
  | ⟨22,_⟩ => exact repair12246Cell22
  | ⟨23,_⟩ => exact repair12246Cell23
  | ⟨24,_⟩ => exact repair12246Cell24
  | ⟨25,_⟩ => exact repair12246Cell25
  | ⟨26,_⟩ => exact repair12246Cell26
  | ⟨27,_⟩ => exact repair12246Cell27
  | ⟨28,_⟩ => exact repair12246Cell28
  | ⟨29,_⟩ => exact repair12246Cell29
  | ⟨30,_⟩ => exact repair12246Cell30
  | ⟨31,_⟩ => exact repair12246Cell31
  | ⟨32,_⟩ => exact repair12246Cell32
  | ⟨33,_⟩ => exact repair12246Cell33
  | ⟨34,_⟩ => exact repair12246Cell34
  | ⟨35,_⟩ => exact repair12246Cell35
  | ⟨36,_⟩ => exact repair12246Cell36
  | ⟨37,_⟩ => exact repair12246Cell37
  | ⟨38,_⟩ => exact repair12246Cell38
  | ⟨39,_⟩ => exact repair12246Cell39
  | ⟨40,_⟩ => exact repair12246Cell40
  | ⟨41,_⟩ => exact repair12246Cell41
  | ⟨42,_⟩ => exact repair12246Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12246 : FrameRepair 12246 scalarRow12246 where
  cap := cap12246
  cap_nonneg := fun j => (repair12246Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12246])
  endpoint := fun j => (repair12246Cells j).2.1
  endpoint_upper := fun j => (repair12246Cells j).2.2.1
  frame := fun j => (repair12246Cells j).2.2.2

noncomputable def cap12247 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275951063 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (17272137 / 62500000 : ℝ)
  | ⟨2,_⟩ => (138378163 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277157461 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138778803 / 500000000 : ℝ)
  | ⟨5,_⟩ => (6948919 / 25000000 : ℝ)
  | ⟨6,_⟩ => (278354453 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278751639 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279147849 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139771543 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279937351 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (35041271 / 125000000 : ℝ)
  | ⟨12,_⟩ => (140361253 / 500000000 : ℝ)
  | ⟨13,_⟩ => (70278349 / 250000000 : ℝ)
  | ⟨14,_⟩ => (281504219 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140946971 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282282721 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (35333821 / 125000000 : ℝ)
  | ⟨18,_⟩ => (70764369 / 250000000 : ℝ)
  | ⟨19,_⟩ => (141721727 / 500000000 : ℝ)
  | ⟨20,_⟩ => (56765701 / 200000000 : ℝ)
  | ⟨21,_⟩ => (142106319 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284595847 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (56995529 / 200000000 : ℝ)
  | ⟨24,_⟩ => (28535903 / 100000000 : ℝ)
  | ⟨25,_⟩ => (285739053 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (28611867 / 100000000 : ℝ)
  | ⟨27,_⟩ => (35812111 / 125000000 : ℝ)
  | ⟨28,_⟩ => (286874209 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143625317 / 500000000 : ℝ)
  | ⟨30,_⟩ => (4494151 / 15625000 : ℝ)
  | ⟨31,_⟩ => (288000309 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288374073 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288746447 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (36139743 / 125000000 : ℝ)
  | ⟨35,_⟩ => (28948857 / 100000000 : ℝ)
  | ⟨36,_⟩ => (144929159 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145113603 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72648807 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145480939 / 500000000 : ℝ)
  | ⟨40,_⟩ => (72831917 / 250000000 : ℝ)
  | ⟨41,_⟩ => (145846303 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292056691 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12247Cell0 :
    0 ≤ cap12247 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨0,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12247 ⟨0,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨0,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell1 :
    0 ≤ cap12247 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨1,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12247 ⟨1,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨1,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell2 :
    0 ≤ cap12247 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨2,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12247 ⟨2,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨2,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell3 :
    0 ≤ cap12247 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨3,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12247 ⟨3,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨3,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell4 :
    0 ≤ cap12247 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨4,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12247 ⟨4,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨4,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell5 :
    0 ≤ cap12247 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨5,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12247 ⟨5,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨5,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell6 :
    0 ≤ cap12247 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨6,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12247 ⟨6,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨6,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell7 :
    0 ≤ cap12247 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨7,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12247 ⟨7,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨7,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell8 :
    0 ≤ cap12247 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨8,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12247 ⟨8,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨8,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell9 :
    0 ≤ cap12247 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨9,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12247 ⟨9,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨9,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell10 :
    0 ≤ cap12247 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨10,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12247 ⟨10,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨10,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell11 :
    0 ≤ cap12247 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨11,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12247 ⟨11,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨11,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell12 :
    0 ≤ cap12247 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨12,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12247 ⟨12,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨12,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell13 :
    0 ≤ cap12247 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨13,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12247 ⟨13,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨13,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell14 :
    0 ≤ cap12247 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨14,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12247 ⟨14,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨14,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell15 :
    0 ≤ cap12247 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨15,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12247 ⟨15,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨15,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell16 :
    0 ≤ cap12247 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨16,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12247 ⟨16,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨16,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell17 :
    0 ≤ cap12247 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨17,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12247 ⟨17,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨17,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell18 :
    0 ≤ cap12247 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨18,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12247 ⟨18,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨18,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell19 :
    0 ≤ cap12247 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨19,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12247 ⟨19,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨19,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell20 :
    0 ≤ cap12247 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨20,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12247 ⟨20,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨20,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell21 :
    0 ≤ cap12247 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨21,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12247 ⟨21,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨21,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell22 :
    0 ≤ cap12247 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨22,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12247 ⟨22,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨22,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell23 :
    0 ≤ cap12247 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨23,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12247 ⟨23,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨23,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell24 :
    0 ≤ cap12247 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨24,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12247 ⟨24,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨24,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell25 :
    0 ≤ cap12247 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨25,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12247 ⟨25,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨25,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell26 :
    0 ≤ cap12247 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨26,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12247 ⟨26,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨26,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell27 :
    0 ≤ cap12247 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨27,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12247 ⟨27,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨27,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell28 :
    0 ≤ cap12247 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨28,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12247 ⟨28,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨28,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell29 :
    0 ≤ cap12247 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨29,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12247 ⟨29,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨29,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell30 :
    0 ≤ cap12247 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨30,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12247 ⟨30,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨30,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell31 :
    0 ≤ cap12247 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨31,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12247 ⟨31,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨31,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell32 :
    0 ≤ cap12247 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨32,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12247 ⟨32,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨32,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell33 :
    0 ≤ cap12247 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨33,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12247 ⟨33,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨33,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell34 :
    0 ≤ cap12247 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨34,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12247 ⟨34,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨34,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell35 :
    0 ≤ cap12247 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨35,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12247 ⟨35,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨35,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell36 :
    0 ≤ cap12247 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨36,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12247 ⟨36,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨36,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell37 :
    0 ≤ cap12247 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨37,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12247 ⟨37,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨37,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell38 :
    0 ≤ cap12247 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨38,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12247 ⟨38,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨38,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell39 :
    0 ≤ cap12247 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨39,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12247 ⟨39,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨39,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell40 :
    0 ≤ cap12247 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨40,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12247 ⟨40,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨40,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell41 :
    0 ≤ cap12247 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨41,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12247 ⟨41,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨41,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cell42 :
    0 ≤ cap12247 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12247 (parameters ⟨42,by decide⟩)
      (scalarRow12247.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12247 ⟨42,by decide⟩ ∧
    (scalarRow12247.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 ⟨42,by decide⟩ + (scalarRow12247.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12247.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12247.targetFrame := by
  norm_num [cap12247, scalarRow12247, sourceIndex, cell12247, BstLean.Part263.envelope, parameters]

theorem repair12247Cells (j : Fin 43) :
    0 ≤ cap12247 j ∧
    BstLean.Part263.envelope 12247 (parameters j) (scalarRow12247.table (sourceIndex j)).upper ≤ cap12247 j ∧
    (scalarRow12247.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12247 j + (scalarRow12247.table (sourceIndex j)).centre) /
      (scalarRow12247.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12247.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12247Cell0
  | ⟨1,_⟩ => exact repair12247Cell1
  | ⟨2,_⟩ => exact repair12247Cell2
  | ⟨3,_⟩ => exact repair12247Cell3
  | ⟨4,_⟩ => exact repair12247Cell4
  | ⟨5,_⟩ => exact repair12247Cell5
  | ⟨6,_⟩ => exact repair12247Cell6
  | ⟨7,_⟩ => exact repair12247Cell7
  | ⟨8,_⟩ => exact repair12247Cell8
  | ⟨9,_⟩ => exact repair12247Cell9
  | ⟨10,_⟩ => exact repair12247Cell10
  | ⟨11,_⟩ => exact repair12247Cell11
  | ⟨12,_⟩ => exact repair12247Cell12
  | ⟨13,_⟩ => exact repair12247Cell13
  | ⟨14,_⟩ => exact repair12247Cell14
  | ⟨15,_⟩ => exact repair12247Cell15
  | ⟨16,_⟩ => exact repair12247Cell16
  | ⟨17,_⟩ => exact repair12247Cell17
  | ⟨18,_⟩ => exact repair12247Cell18
  | ⟨19,_⟩ => exact repair12247Cell19
  | ⟨20,_⟩ => exact repair12247Cell20
  | ⟨21,_⟩ => exact repair12247Cell21
  | ⟨22,_⟩ => exact repair12247Cell22
  | ⟨23,_⟩ => exact repair12247Cell23
  | ⟨24,_⟩ => exact repair12247Cell24
  | ⟨25,_⟩ => exact repair12247Cell25
  | ⟨26,_⟩ => exact repair12247Cell26
  | ⟨27,_⟩ => exact repair12247Cell27
  | ⟨28,_⟩ => exact repair12247Cell28
  | ⟨29,_⟩ => exact repair12247Cell29
  | ⟨30,_⟩ => exact repair12247Cell30
  | ⟨31,_⟩ => exact repair12247Cell31
  | ⟨32,_⟩ => exact repair12247Cell32
  | ⟨33,_⟩ => exact repair12247Cell33
  | ⟨34,_⟩ => exact repair12247Cell34
  | ⟨35,_⟩ => exact repair12247Cell35
  | ⟨36,_⟩ => exact repair12247Cell36
  | ⟨37,_⟩ => exact repair12247Cell37
  | ⟨38,_⟩ => exact repair12247Cell38
  | ⟨39,_⟩ => exact repair12247Cell39
  | ⟨40,_⟩ => exact repair12247Cell40
  | ⟨41,_⟩ => exact repair12247Cell41
  | ⟨42,_⟩ => exact repair12247Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12247 : FrameRepair 12247 scalarRow12247 where
  cap := cap12247
  cap_nonneg := fun j => (repair12247Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12247])
  endpoint := fun j => (repair12247Cells j).2.1
  endpoint_upper := fun j => (repair12247Cells j).2.2.1
  frame := fun j => (repair12247Cells j).2.2.2

noncomputable def cap12248 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275950987 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276354109 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276756237 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138578683 / 500000000 : ℝ)
  | ⟨4,_⟩ => (1084209 / 3906250 : ℝ)
  | ⟨5,_⟩ => (69489163 / 250000000 : ℝ)
  | ⟨6,_⟩ => (278354339 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139375759 / 500000000 : ℝ)
  | ⟨8,_⟩ => (139573861 / 500000000 : ℝ)
  | ⟨9,_⟩ => (34942869 / 125000000 : ℝ)
  | ⟨10,_⟩ => (279937211 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280330021 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280722353 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281113237 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281504053 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (28189377 / 100000000 : ℝ)
  | ⟨16,_⟩ => (282282543 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (17666899 / 62500000 : ℝ)
  | ⟨18,_⟩ => (56611457 / 200000000 : ℝ)
  | ⟨19,_⟩ => (283443257 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283828301 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284212429 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (17787227 / 62500000 : ℝ)
  | ⟨23,_⟩ => (284977423 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285358801 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142869409 / 500000000 : ℝ)
  | ⟨26,_⟩ => (28611843 / 100000000 : ℝ)
  | ⟨27,_⟩ => (286496641 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (71718489 / 250000000 : ℝ)
  | ⟨29,_⟩ => (143625187 / 500000000 : ℝ)
  | ⟨30,_⟩ => (287625399 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (144000019 / 500000000 : ℝ)
  | ⟨32,_⟩ => (72093449 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288746163 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (57823531 / 200000000 : ℝ)
  | ⟨35,_⟩ => (144744137 / 500000000 : ℝ)
  | ⟨36,_⟩ => (9058063 / 31250000 : ℝ)
  | ⟨37,_⟩ => (145113449 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145297457 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145480779 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145663671 / 500000000 : ℝ)
  | ⟨41,_⟩ => (145846137 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292056353 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12248Cell0 :
    0 ≤ cap12248 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨0,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12248 ⟨0,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨0,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell1 :
    0 ≤ cap12248 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨1,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12248 ⟨1,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨1,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell2 :
    0 ≤ cap12248 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨2,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12248 ⟨2,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨2,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell3 :
    0 ≤ cap12248 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨3,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12248 ⟨3,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨3,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell4 :
    0 ≤ cap12248 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨4,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12248 ⟨4,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨4,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell5 :
    0 ≤ cap12248 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨5,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12248 ⟨5,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨5,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell6 :
    0 ≤ cap12248 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨6,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12248 ⟨6,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨6,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell7 :
    0 ≤ cap12248 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨7,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12248 ⟨7,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨7,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell8 :
    0 ≤ cap12248 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨8,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12248 ⟨8,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨8,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell9 :
    0 ≤ cap12248 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨9,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12248 ⟨9,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨9,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell10 :
    0 ≤ cap12248 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨10,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12248 ⟨10,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨10,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell11 :
    0 ≤ cap12248 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨11,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12248 ⟨11,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨11,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell12 :
    0 ≤ cap12248 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨12,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12248 ⟨12,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨12,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell13 :
    0 ≤ cap12248 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨13,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12248 ⟨13,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨13,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell14 :
    0 ≤ cap12248 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨14,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12248 ⟨14,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨14,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell15 :
    0 ≤ cap12248 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨15,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12248 ⟨15,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨15,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell16 :
    0 ≤ cap12248 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨16,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12248 ⟨16,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨16,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell17 :
    0 ≤ cap12248 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨17,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12248 ⟨17,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨17,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell18 :
    0 ≤ cap12248 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨18,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12248 ⟨18,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨18,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell19 :
    0 ≤ cap12248 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨19,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12248 ⟨19,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨19,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell20 :
    0 ≤ cap12248 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨20,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12248 ⟨20,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨20,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell21 :
    0 ≤ cap12248 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨21,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12248 ⟨21,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨21,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell22 :
    0 ≤ cap12248 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨22,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12248 ⟨22,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨22,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell23 :
    0 ≤ cap12248 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨23,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12248 ⟨23,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨23,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell24 :
    0 ≤ cap12248 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨24,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12248 ⟨24,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨24,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell25 :
    0 ≤ cap12248 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨25,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12248 ⟨25,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨25,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell26 :
    0 ≤ cap12248 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨26,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12248 ⟨26,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨26,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell27 :
    0 ≤ cap12248 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨27,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12248 ⟨27,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨27,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell28 :
    0 ≤ cap12248 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨28,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12248 ⟨28,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨28,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell29 :
    0 ≤ cap12248 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨29,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12248 ⟨29,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨29,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell30 :
    0 ≤ cap12248 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨30,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12248 ⟨30,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨30,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell31 :
    0 ≤ cap12248 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨31,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12248 ⟨31,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨31,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell32 :
    0 ≤ cap12248 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨32,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12248 ⟨32,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨32,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell33 :
    0 ≤ cap12248 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨33,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12248 ⟨33,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨33,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell34 :
    0 ≤ cap12248 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨34,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12248 ⟨34,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨34,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell35 :
    0 ≤ cap12248 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨35,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12248 ⟨35,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨35,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell36 :
    0 ≤ cap12248 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨36,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12248 ⟨36,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨36,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell37 :
    0 ≤ cap12248 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨37,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12248 ⟨37,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨37,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell38 :
    0 ≤ cap12248 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨38,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12248 ⟨38,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨38,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell39 :
    0 ≤ cap12248 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨39,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12248 ⟨39,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨39,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell40 :
    0 ≤ cap12248 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨40,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12248 ⟨40,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨40,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell41 :
    0 ≤ cap12248 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨41,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12248 ⟨41,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨41,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cell42 :
    0 ≤ cap12248 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12248 (parameters ⟨42,by decide⟩)
      (scalarRow12248.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12248 ⟨42,by decide⟩ ∧
    (scalarRow12248.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 ⟨42,by decide⟩ + (scalarRow12248.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12248.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12248.targetFrame := by
  norm_num [cap12248, scalarRow12248, sourceIndex, cell12248, BstLean.Part263.envelope, parameters]

theorem repair12248Cells (j : Fin 43) :
    0 ≤ cap12248 j ∧
    BstLean.Part263.envelope 12248 (parameters j) (scalarRow12248.table (sourceIndex j)).upper ≤ cap12248 j ∧
    (scalarRow12248.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12248 j + (scalarRow12248.table (sourceIndex j)).centre) /
      (scalarRow12248.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12248.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12248Cell0
  | ⟨1,_⟩ => exact repair12248Cell1
  | ⟨2,_⟩ => exact repair12248Cell2
  | ⟨3,_⟩ => exact repair12248Cell3
  | ⟨4,_⟩ => exact repair12248Cell4
  | ⟨5,_⟩ => exact repair12248Cell5
  | ⟨6,_⟩ => exact repair12248Cell6
  | ⟨7,_⟩ => exact repair12248Cell7
  | ⟨8,_⟩ => exact repair12248Cell8
  | ⟨9,_⟩ => exact repair12248Cell9
  | ⟨10,_⟩ => exact repair12248Cell10
  | ⟨11,_⟩ => exact repair12248Cell11
  | ⟨12,_⟩ => exact repair12248Cell12
  | ⟨13,_⟩ => exact repair12248Cell13
  | ⟨14,_⟩ => exact repair12248Cell14
  | ⟨15,_⟩ => exact repair12248Cell15
  | ⟨16,_⟩ => exact repair12248Cell16
  | ⟨17,_⟩ => exact repair12248Cell17
  | ⟨18,_⟩ => exact repair12248Cell18
  | ⟨19,_⟩ => exact repair12248Cell19
  | ⟨20,_⟩ => exact repair12248Cell20
  | ⟨21,_⟩ => exact repair12248Cell21
  | ⟨22,_⟩ => exact repair12248Cell22
  | ⟨23,_⟩ => exact repair12248Cell23
  | ⟨24,_⟩ => exact repair12248Cell24
  | ⟨25,_⟩ => exact repair12248Cell25
  | ⟨26,_⟩ => exact repair12248Cell26
  | ⟨27,_⟩ => exact repair12248Cell27
  | ⟨28,_⟩ => exact repair12248Cell28
  | ⟨29,_⟩ => exact repair12248Cell29
  | ⟨30,_⟩ => exact repair12248Cell30
  | ⟨31,_⟩ => exact repair12248Cell31
  | ⟨32,_⟩ => exact repair12248Cell32
  | ⟨33,_⟩ => exact repair12248Cell33
  | ⟨34,_⟩ => exact repair12248Cell34
  | ⟨35,_⟩ => exact repair12248Cell35
  | ⟨36,_⟩ => exact repair12248Cell36
  | ⟨37,_⟩ => exact repair12248Cell37
  | ⟨38,_⟩ => exact repair12248Cell38
  | ⟨39,_⟩ => exact repair12248Cell39
  | ⟨40,_⟩ => exact repair12248Cell40
  | ⟨41,_⟩ => exact repair12248Cell41
  | ⟨42,_⟩ => exact repair12248Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12248 : FrameRepair 12248 scalarRow12248 where
  cap := cap12248
  cap_nonneg := fun j => (repair12248Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12248])
  endpoint := fun j => (repair12248Cells j).2.1
  endpoint_upper := fun j => (repair12248Cells j).2.2.1
  frame := fun j => (repair12248Cells j).2.2.2

noncomputable def cap12249 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275950911 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276354027 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (69189037 / 250000000 : ℝ)
  | ⟨3,_⟩ => (277157271 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138778701 / 500000000 : ℝ)
  | ⟨5,_⟩ => (4343071 / 15625000 : ℝ)
  | ⟨6,_⟩ => (17397139 / 62500000 : ℝ)
  | ⟨7,_⟩ => (278751397 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139573797 / 500000000 : ℝ)
  | ⟨9,_⟩ => (139771409 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279937071 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140164937 / 500000000 : ℝ)
  | ⟨12,_⟩ => (1403611 / 5000000 : ℝ)
  | ⟨13,_⟩ => (140556539 / 500000000 : ℝ)
  | ⟨14,_⟩ => (17593993 / 62500000 : ℝ)
  | ⟨15,_⟩ => (140946799 / 500000000 : ℝ)
  | ⟨16,_⟩ => (70570591 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282670199 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141528547 / 500000000 : ℝ)
  | ⟨19,_⟩ => (14172153 / 50000000 : ℝ)
  | ⟨20,_⟩ => (141914049 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284212219 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (35574427 / 125000000 : ℝ)
  | ⟨23,_⟩ => (284977201 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285358573 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (35717323 / 125000000 : ℝ)
  | ⟨26,_⟩ => (286118189 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (57299279 / 200000000 : ℝ)
  | ⟨28,_⟩ => (286873703 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (57450023 / 200000000 : ℝ)
  | ⟨30,_⟩ => (287625133 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287999767 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288373519 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (7218647 / 25000000 : ℝ)
  | ⟨34,_⟩ => (57823473 / 200000000 : ℝ)
  | ⟨35,_⟩ => (144743989 / 500000000 : ℝ)
  | ⟨36,_⟩ => (144928857 / 500000000 : ℝ)
  | ⟨37,_⟩ => (29022659 / 100000000 : ℝ)
  | ⟨38,_⟩ => (290594601 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145480619 / 500000000 : ℝ)
  | ⟨40,_⟩ => (36415877 / 125000000 : ℝ)
  | ⟨41,_⟩ => (145845971 / 500000000 : ℝ)
  | ⟨42,_⟩ => (18253501 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12249Cell0 :
    0 ≤ cap12249 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨0,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12249 ⟨0,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨0,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell1 :
    0 ≤ cap12249 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨1,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12249 ⟨1,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨1,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell2 :
    0 ≤ cap12249 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨2,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12249 ⟨2,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨2,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell3 :
    0 ≤ cap12249 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨3,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12249 ⟨3,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨3,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell4 :
    0 ≤ cap12249 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨4,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12249 ⟨4,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨4,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell5 :
    0 ≤ cap12249 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨5,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12249 ⟨5,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨5,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell6 :
    0 ≤ cap12249 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨6,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12249 ⟨6,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨6,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell7 :
    0 ≤ cap12249 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨7,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12249 ⟨7,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨7,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell8 :
    0 ≤ cap12249 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨8,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12249 ⟨8,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨8,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell9 :
    0 ≤ cap12249 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨9,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12249 ⟨9,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨9,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell10 :
    0 ≤ cap12249 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨10,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12249 ⟨10,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨10,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell11 :
    0 ≤ cap12249 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨11,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12249 ⟨11,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨11,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell12 :
    0 ≤ cap12249 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨12,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12249 ⟨12,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨12,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell13 :
    0 ≤ cap12249 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨13,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12249 ⟨13,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨13,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell14 :
    0 ≤ cap12249 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨14,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12249 ⟨14,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨14,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell15 :
    0 ≤ cap12249 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨15,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12249 ⟨15,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨15,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell16 :
    0 ≤ cap12249 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨16,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12249 ⟨16,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨16,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell17 :
    0 ≤ cap12249 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨17,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12249 ⟨17,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨17,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell18 :
    0 ≤ cap12249 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨18,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12249 ⟨18,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨18,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell19 :
    0 ≤ cap12249 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨19,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12249 ⟨19,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨19,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell20 :
    0 ≤ cap12249 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨20,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12249 ⟨20,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨20,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell21 :
    0 ≤ cap12249 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨21,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12249 ⟨21,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨21,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell22 :
    0 ≤ cap12249 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨22,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12249 ⟨22,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨22,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell23 :
    0 ≤ cap12249 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨23,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12249 ⟨23,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨23,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell24 :
    0 ≤ cap12249 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨24,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12249 ⟨24,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨24,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell25 :
    0 ≤ cap12249 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨25,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12249 ⟨25,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨25,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell26 :
    0 ≤ cap12249 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨26,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12249 ⟨26,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨26,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell27 :
    0 ≤ cap12249 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨27,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12249 ⟨27,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨27,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell28 :
    0 ≤ cap12249 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨28,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12249 ⟨28,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨28,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell29 :
    0 ≤ cap12249 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨29,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12249 ⟨29,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨29,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell30 :
    0 ≤ cap12249 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨30,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12249 ⟨30,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨30,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell31 :
    0 ≤ cap12249 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨31,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12249 ⟨31,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨31,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell32 :
    0 ≤ cap12249 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨32,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12249 ⟨32,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨32,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell33 :
    0 ≤ cap12249 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨33,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12249 ⟨33,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨33,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell34 :
    0 ≤ cap12249 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨34,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12249 ⟨34,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨34,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell35 :
    0 ≤ cap12249 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨35,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12249 ⟨35,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨35,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell36 :
    0 ≤ cap12249 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨36,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12249 ⟨36,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨36,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell37 :
    0 ≤ cap12249 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨37,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12249 ⟨37,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨37,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell38 :
    0 ≤ cap12249 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨38,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12249 ⟨38,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨38,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell39 :
    0 ≤ cap12249 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨39,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12249 ⟨39,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨39,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell40 :
    0 ≤ cap12249 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨40,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12249 ⟨40,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨40,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell41 :
    0 ≤ cap12249 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨41,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12249 ⟨41,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨41,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cell42 :
    0 ≤ cap12249 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12249 (parameters ⟨42,by decide⟩)
      (scalarRow12249.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12249 ⟨42,by decide⟩ ∧
    (scalarRow12249.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 ⟨42,by decide⟩ + (scalarRow12249.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12249.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12249.targetFrame := by
  norm_num [cap12249, scalarRow12249, sourceIndex, cell12249, BstLean.Part263.envelope, parameters]

theorem repair12249Cells (j : Fin 43) :
    0 ≤ cap12249 j ∧
    BstLean.Part263.envelope 12249 (parameters j) (scalarRow12249.table (sourceIndex j)).upper ≤ cap12249 j ∧
    (scalarRow12249.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12249 j + (scalarRow12249.table (sourceIndex j)).centre) /
      (scalarRow12249.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12249.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12249Cell0
  | ⟨1,_⟩ => exact repair12249Cell1
  | ⟨2,_⟩ => exact repair12249Cell2
  | ⟨3,_⟩ => exact repair12249Cell3
  | ⟨4,_⟩ => exact repair12249Cell4
  | ⟨5,_⟩ => exact repair12249Cell5
  | ⟨6,_⟩ => exact repair12249Cell6
  | ⟨7,_⟩ => exact repair12249Cell7
  | ⟨8,_⟩ => exact repair12249Cell8
  | ⟨9,_⟩ => exact repair12249Cell9
  | ⟨10,_⟩ => exact repair12249Cell10
  | ⟨11,_⟩ => exact repair12249Cell11
  | ⟨12,_⟩ => exact repair12249Cell12
  | ⟨13,_⟩ => exact repair12249Cell13
  | ⟨14,_⟩ => exact repair12249Cell14
  | ⟨15,_⟩ => exact repair12249Cell15
  | ⟨16,_⟩ => exact repair12249Cell16
  | ⟨17,_⟩ => exact repair12249Cell17
  | ⟨18,_⟩ => exact repair12249Cell18
  | ⟨19,_⟩ => exact repair12249Cell19
  | ⟨20,_⟩ => exact repair12249Cell20
  | ⟨21,_⟩ => exact repair12249Cell21
  | ⟨22,_⟩ => exact repair12249Cell22
  | ⟨23,_⟩ => exact repair12249Cell23
  | ⟨24,_⟩ => exact repair12249Cell24
  | ⟨25,_⟩ => exact repair12249Cell25
  | ⟨26,_⟩ => exact repair12249Cell26
  | ⟨27,_⟩ => exact repair12249Cell27
  | ⟨28,_⟩ => exact repair12249Cell28
  | ⟨29,_⟩ => exact repair12249Cell29
  | ⟨30,_⟩ => exact repair12249Cell30
  | ⟨31,_⟩ => exact repair12249Cell31
  | ⟨32,_⟩ => exact repair12249Cell32
  | ⟨33,_⟩ => exact repair12249Cell33
  | ⟨34,_⟩ => exact repair12249Cell34
  | ⟨35,_⟩ => exact repair12249Cell35
  | ⟨36,_⟩ => exact repair12249Cell36
  | ⟨37,_⟩ => exact repair12249Cell37
  | ⟨38,_⟩ => exact repair12249Cell38
  | ⟨39,_⟩ => exact repair12249Cell39
  | ⟨40,_⟩ => exact repair12249Cell40
  | ⟨41,_⟩ => exact repair12249Cell41
  | ⟨42,_⟩ => exact repair12249Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12249 : FrameRepair 12249 scalarRow12249 where
  cap := cap12249
  cap_nonneg := fun j => (repair12249Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12249])
  endpoint := fun j => (repair12249Cells j).2.1
  endpoint_upper := fun j => (repair12249Cells j).2.2.1
  frame := fun j => (repair12249Cells j).2.2.2


end BstLean.Part264
