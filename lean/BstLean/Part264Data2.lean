import BstLean.Part264Repair
/-! Rational envelope and frame checks for each dimension. -/
namespace BstLean.Part264
open Real Set BstLean.Part255 BstLean.Part263
noncomputable def cap12275 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275948943 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (27635189 / 100000000 : ℝ)
  | ⟨2,_⟩ => (138376921 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277154797 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277554761 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (55590747 / 200000000 : ℝ)
  | ⟨6,_⟩ => (278351247 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139374127 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69786071 / 250000000 : ℝ)
  | ⟨9,_⟩ => (139769671 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279933429 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280326067 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (70179557 / 250000000 : ℝ)
  | ⟨13,_⟩ => (281108941 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281499587 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281889133 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (35284717 / 125000000 : ℝ)
  | ⟨17,_⟩ => (282665407 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283052139 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141718971 / 500000000 : ℝ)
  | ⟨20,_⟩ => (141911409 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284206777 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (71147453 / 250000000 : ℝ)
  | ⟨23,_⟩ => (71242859 / 250000000 : ℝ)
  | ⟨24,_⟩ => (35669081 / 125000000 : ℝ)
  | ⟨25,_⟩ => (285732497 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286111943 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71622497 / 250000000 : ℝ)
  | ⟨28,_⟩ => (286867137 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (28724339 / 100000000 : ℝ)
  | ⟨30,_⟩ => (1150473 / 4000000 : ℝ)
  | ⟨31,_⟩ => (71998181 / 250000000 : ℝ)
  | ⟨32,_⟩ => (144183159 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288738521 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289109849 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (57896061 / 200000000 : ℝ)
  | ⟨36,_⟩ => (72462471 / 250000000 : ℝ)
  | ⟨37,_⟩ => (72554651 / 250000000 : ℝ)
  | ⟨38,_⟩ => (145293229 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290952939 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145659281 / 500000000 : ℝ)
  | ⟨41,_⟩ => (72920833 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292047251 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12275Cell0 :
    0 ≤ cap12275 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨0,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12275 ⟨0,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨0,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell1 :
    0 ≤ cap12275 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨1,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12275 ⟨1,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨1,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell2 :
    0 ≤ cap12275 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨2,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12275 ⟨2,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨2,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell3 :
    0 ≤ cap12275 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨3,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12275 ⟨3,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨3,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell4 :
    0 ≤ cap12275 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨4,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12275 ⟨4,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨4,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell5 :
    0 ≤ cap12275 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨5,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12275 ⟨5,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨5,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell6 :
    0 ≤ cap12275 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨6,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12275 ⟨6,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨6,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell7 :
    0 ≤ cap12275 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨7,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12275 ⟨7,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨7,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell8 :
    0 ≤ cap12275 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨8,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12275 ⟨8,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨8,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell9 :
    0 ≤ cap12275 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨9,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12275 ⟨9,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨9,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell10 :
    0 ≤ cap12275 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨10,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12275 ⟨10,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨10,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell11 :
    0 ≤ cap12275 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨11,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12275 ⟨11,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨11,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell12 :
    0 ≤ cap12275 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨12,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12275 ⟨12,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨12,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell13 :
    0 ≤ cap12275 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨13,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12275 ⟨13,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨13,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell14 :
    0 ≤ cap12275 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨14,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12275 ⟨14,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨14,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell15 :
    0 ≤ cap12275 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨15,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12275 ⟨15,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨15,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell16 :
    0 ≤ cap12275 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨16,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12275 ⟨16,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨16,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell17 :
    0 ≤ cap12275 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨17,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12275 ⟨17,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨17,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell18 :
    0 ≤ cap12275 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨18,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12275 ⟨18,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨18,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell19 :
    0 ≤ cap12275 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨19,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12275 ⟨19,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨19,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell20 :
    0 ≤ cap12275 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨20,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12275 ⟨20,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨20,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell21 :
    0 ≤ cap12275 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨21,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12275 ⟨21,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨21,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell22 :
    0 ≤ cap12275 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨22,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12275 ⟨22,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨22,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell23 :
    0 ≤ cap12275 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨23,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12275 ⟨23,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨23,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell24 :
    0 ≤ cap12275 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨24,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12275 ⟨24,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨24,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell25 :
    0 ≤ cap12275 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨25,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12275 ⟨25,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨25,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell26 :
    0 ≤ cap12275 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨26,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12275 ⟨26,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨26,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell27 :
    0 ≤ cap12275 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨27,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12275 ⟨27,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨27,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell28 :
    0 ≤ cap12275 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨28,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12275 ⟨28,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨28,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell29 :
    0 ≤ cap12275 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨29,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12275 ⟨29,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨29,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell30 :
    0 ≤ cap12275 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨30,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12275 ⟨30,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨30,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell31 :
    0 ≤ cap12275 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨31,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12275 ⟨31,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨31,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell32 :
    0 ≤ cap12275 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨32,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12275 ⟨32,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨32,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell33 :
    0 ≤ cap12275 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨33,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12275 ⟨33,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨33,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell34 :
    0 ≤ cap12275 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨34,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12275 ⟨34,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨34,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell35 :
    0 ≤ cap12275 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨35,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12275 ⟨35,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨35,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell36 :
    0 ≤ cap12275 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨36,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12275 ⟨36,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨36,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell37 :
    0 ≤ cap12275 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨37,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12275 ⟨37,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨37,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell38 :
    0 ≤ cap12275 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨38,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12275 ⟨38,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨38,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell39 :
    0 ≤ cap12275 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨39,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12275 ⟨39,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨39,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell40 :
    0 ≤ cap12275 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨40,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12275 ⟨40,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨40,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell41 :
    0 ≤ cap12275 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨41,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12275 ⟨41,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨41,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cell42 :
    0 ≤ cap12275 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12275 (parameters ⟨42,by decide⟩)
      (scalarRow12275.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12275 ⟨42,by decide⟩ ∧
    (scalarRow12275.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 ⟨42,by decide⟩ + (scalarRow12275.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12275.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12275.targetFrame := by
  norm_num [cap12275, scalarRow12275, sourceIndex, cell12275, BstLean.Part263.envelope, parameters]

theorem repair12275Cells (j : Fin 43) :
    0 ≤ cap12275 j ∧
    BstLean.Part263.envelope 12275 (parameters j) (scalarRow12275.table (sourceIndex j)).upper ≤ cap12275 j ∧
    (scalarRow12275.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12275 j + (scalarRow12275.table (sourceIndex j)).centre) /
      (scalarRow12275.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12275.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12275Cell0
  | ⟨1,_⟩ => exact repair12275Cell1
  | ⟨2,_⟩ => exact repair12275Cell2
  | ⟨3,_⟩ => exact repair12275Cell3
  | ⟨4,_⟩ => exact repair12275Cell4
  | ⟨5,_⟩ => exact repair12275Cell5
  | ⟨6,_⟩ => exact repair12275Cell6
  | ⟨7,_⟩ => exact repair12275Cell7
  | ⟨8,_⟩ => exact repair12275Cell8
  | ⟨9,_⟩ => exact repair12275Cell9
  | ⟨10,_⟩ => exact repair12275Cell10
  | ⟨11,_⟩ => exact repair12275Cell11
  | ⟨12,_⟩ => exact repair12275Cell12
  | ⟨13,_⟩ => exact repair12275Cell13
  | ⟨14,_⟩ => exact repair12275Cell14
  | ⟨15,_⟩ => exact repair12275Cell15
  | ⟨16,_⟩ => exact repair12275Cell16
  | ⟨17,_⟩ => exact repair12275Cell17
  | ⟨18,_⟩ => exact repair12275Cell18
  | ⟨19,_⟩ => exact repair12275Cell19
  | ⟨20,_⟩ => exact repair12275Cell20
  | ⟨21,_⟩ => exact repair12275Cell21
  | ⟨22,_⟩ => exact repair12275Cell22
  | ⟨23,_⟩ => exact repair12275Cell23
  | ⟨24,_⟩ => exact repair12275Cell24
  | ⟨25,_⟩ => exact repair12275Cell25
  | ⟨26,_⟩ => exact repair12275Cell26
  | ⟨27,_⟩ => exact repair12275Cell27
  | ⟨28,_⟩ => exact repair12275Cell28
  | ⟨29,_⟩ => exact repair12275Cell29
  | ⟨30,_⟩ => exact repair12275Cell30
  | ⟨31,_⟩ => exact repair12275Cell31
  | ⟨32,_⟩ => exact repair12275Cell32
  | ⟨33,_⟩ => exact repair12275Cell33
  | ⟨34,_⟩ => exact repair12275Cell34
  | ⟨35,_⟩ => exact repair12275Cell35
  | ⟨36,_⟩ => exact repair12275Cell36
  | ⟨37,_⟩ => exact repair12275Cell37
  | ⟨38,_⟩ => exact repair12275Cell38
  | ⟨39,_⟩ => exact repair12275Cell39
  | ⟨40,_⟩ => exact repair12275Cell40
  | ⟨41,_⟩ => exact repair12275Cell41
  | ⟨42,_⟩ => exact repair12275Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12275 : FrameRepair 12275 scalarRow12275 where
  cap := cap12275
  cap_nonneg := fun j => (repair12275Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12275])
  endpoint := fun j => (repair12275Cells j).2.1
  endpoint_upper := fun j => (repair12275Cells j).2.2.1
  frame := fun j => (repair12275Cells j).2.2.2

noncomputable def cap12276 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68987217 / 250000000 : ℝ)
  | ⟨1,_⟩ => (4317997 / 15625000 : ℝ)
  | ⟨2,_⟩ => (138376877 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138577351 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277554659 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277953627 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278351133 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278748133 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279144157 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279539209 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279933289 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280325921 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (11228723 / 40000000 : ℝ)
  | ⟨13,_⟩ => (140554391 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140749711 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281888961 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (141138779 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282665223 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283051949 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141718873 / 500000000 : ℝ)
  | ⟨20,_⟩ => (56764523 / 200000000 : ℝ)
  | ⟨21,_⟩ => (35525821 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284589597 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (56994243 / 200000000 : ℝ)
  | ⟨24,_⟩ => (14267621 / 50000000 : ℝ)
  | ⟨25,_⟩ => (35716533 / 125000000 : ℝ)
  | ⟨26,_⟩ => (286111703 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143244871 / 500000000 : ℝ)
  | ⟨28,_⟩ => (57373377 / 200000000 : ℝ)
  | ⟨29,_⟩ => (71810783 / 250000000 : ℝ)
  | ⟨30,_⟩ => (57523597 / 200000000 : ℝ)
  | ⟨31,_⟩ => (143996227 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288366041 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288738239 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (7227739 / 25000000 : ℝ)
  | ⟨35,_⟩ => (28948001 / 100000000 : ℝ)
  | ⟨36,_⟩ => (289849583 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290218297 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (58117229 / 200000000 : ℝ)
  | ⟨39,_⟩ => (290952621 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291318237 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145841501 / 500000000 : ℝ)
  | ⟨42,_⟩ => (58409383 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12276Cell0 :
    0 ≤ cap12276 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨0,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12276 ⟨0,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨0,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell1 :
    0 ≤ cap12276 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨1,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12276 ⟨1,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨1,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell2 :
    0 ≤ cap12276 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨2,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12276 ⟨2,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨2,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell3 :
    0 ≤ cap12276 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨3,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12276 ⟨3,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨3,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell4 :
    0 ≤ cap12276 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨4,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12276 ⟨4,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨4,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell5 :
    0 ≤ cap12276 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨5,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12276 ⟨5,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨5,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell6 :
    0 ≤ cap12276 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨6,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12276 ⟨6,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨6,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell7 :
    0 ≤ cap12276 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨7,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12276 ⟨7,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨7,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell8 :
    0 ≤ cap12276 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨8,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12276 ⟨8,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨8,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell9 :
    0 ≤ cap12276 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨9,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12276 ⟨9,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨9,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell10 :
    0 ≤ cap12276 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨10,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12276 ⟨10,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨10,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell11 :
    0 ≤ cap12276 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨11,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12276 ⟨11,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨11,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell12 :
    0 ≤ cap12276 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨12,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12276 ⟨12,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨12,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell13 :
    0 ≤ cap12276 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨13,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12276 ⟨13,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨13,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell14 :
    0 ≤ cap12276 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨14,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12276 ⟨14,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨14,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell15 :
    0 ≤ cap12276 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨15,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12276 ⟨15,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨15,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell16 :
    0 ≤ cap12276 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨16,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12276 ⟨16,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨16,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell17 :
    0 ≤ cap12276 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨17,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12276 ⟨17,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨17,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell18 :
    0 ≤ cap12276 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨18,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12276 ⟨18,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨18,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell19 :
    0 ≤ cap12276 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨19,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12276 ⟨19,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨19,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell20 :
    0 ≤ cap12276 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨20,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12276 ⟨20,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨20,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell21 :
    0 ≤ cap12276 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨21,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12276 ⟨21,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨21,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell22 :
    0 ≤ cap12276 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨22,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12276 ⟨22,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨22,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell23 :
    0 ≤ cap12276 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨23,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12276 ⟨23,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨23,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell24 :
    0 ≤ cap12276 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨24,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12276 ⟨24,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨24,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell25 :
    0 ≤ cap12276 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨25,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12276 ⟨25,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨25,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell26 :
    0 ≤ cap12276 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨26,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12276 ⟨26,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨26,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell27 :
    0 ≤ cap12276 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨27,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12276 ⟨27,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨27,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell28 :
    0 ≤ cap12276 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨28,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12276 ⟨28,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨28,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell29 :
    0 ≤ cap12276 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨29,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12276 ⟨29,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨29,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell30 :
    0 ≤ cap12276 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨30,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12276 ⟨30,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨30,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell31 :
    0 ≤ cap12276 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨31,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12276 ⟨31,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨31,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell32 :
    0 ≤ cap12276 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨32,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12276 ⟨32,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨32,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell33 :
    0 ≤ cap12276 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨33,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12276 ⟨33,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨33,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell34 :
    0 ≤ cap12276 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨34,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12276 ⟨34,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨34,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell35 :
    0 ≤ cap12276 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨35,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12276 ⟨35,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨35,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell36 :
    0 ≤ cap12276 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨36,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12276 ⟨36,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨36,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell37 :
    0 ≤ cap12276 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨37,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12276 ⟨37,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨37,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell38 :
    0 ≤ cap12276 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨38,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12276 ⟨38,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨38,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell39 :
    0 ≤ cap12276 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨39,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12276 ⟨39,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨39,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell40 :
    0 ≤ cap12276 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨40,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12276 ⟨40,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨40,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell41 :
    0 ≤ cap12276 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨41,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12276 ⟨41,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨41,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cell42 :
    0 ≤ cap12276 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12276 (parameters ⟨42,by decide⟩)
      (scalarRow12276.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12276 ⟨42,by decide⟩ ∧
    (scalarRow12276.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 ⟨42,by decide⟩ + (scalarRow12276.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12276.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12276.targetFrame := by
  norm_num [cap12276, scalarRow12276, sourceIndex, cell12276, BstLean.Part263.envelope, parameters]

theorem repair12276Cells (j : Fin 43) :
    0 ≤ cap12276 j ∧
    BstLean.Part263.envelope 12276 (parameters j) (scalarRow12276.table (sourceIndex j)).upper ≤ cap12276 j ∧
    (scalarRow12276.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12276 j + (scalarRow12276.table (sourceIndex j)).centre) /
      (scalarRow12276.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12276.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12276Cell0
  | ⟨1,_⟩ => exact repair12276Cell1
  | ⟨2,_⟩ => exact repair12276Cell2
  | ⟨3,_⟩ => exact repair12276Cell3
  | ⟨4,_⟩ => exact repair12276Cell4
  | ⟨5,_⟩ => exact repair12276Cell5
  | ⟨6,_⟩ => exact repair12276Cell6
  | ⟨7,_⟩ => exact repair12276Cell7
  | ⟨8,_⟩ => exact repair12276Cell8
  | ⟨9,_⟩ => exact repair12276Cell9
  | ⟨10,_⟩ => exact repair12276Cell10
  | ⟨11,_⟩ => exact repair12276Cell11
  | ⟨12,_⟩ => exact repair12276Cell12
  | ⟨13,_⟩ => exact repair12276Cell13
  | ⟨14,_⟩ => exact repair12276Cell14
  | ⟨15,_⟩ => exact repair12276Cell15
  | ⟨16,_⟩ => exact repair12276Cell16
  | ⟨17,_⟩ => exact repair12276Cell17
  | ⟨18,_⟩ => exact repair12276Cell18
  | ⟨19,_⟩ => exact repair12276Cell19
  | ⟨20,_⟩ => exact repair12276Cell20
  | ⟨21,_⟩ => exact repair12276Cell21
  | ⟨22,_⟩ => exact repair12276Cell22
  | ⟨23,_⟩ => exact repair12276Cell23
  | ⟨24,_⟩ => exact repair12276Cell24
  | ⟨25,_⟩ => exact repair12276Cell25
  | ⟨26,_⟩ => exact repair12276Cell26
  | ⟨27,_⟩ => exact repair12276Cell27
  | ⟨28,_⟩ => exact repair12276Cell28
  | ⟨29,_⟩ => exact repair12276Cell29
  | ⟨30,_⟩ => exact repair12276Cell30
  | ⟨31,_⟩ => exact repair12276Cell31
  | ⟨32,_⟩ => exact repair12276Cell32
  | ⟨33,_⟩ => exact repair12276Cell33
  | ⟨34,_⟩ => exact repair12276Cell34
  | ⟨35,_⟩ => exact repair12276Cell35
  | ⟨36,_⟩ => exact repair12276Cell36
  | ⟨37,_⟩ => exact repair12276Cell37
  | ⟨38,_⟩ => exact repair12276Cell38
  | ⟨39,_⟩ => exact repair12276Cell39
  | ⟨40,_⟩ => exact repair12276Cell40
  | ⟨41,_⟩ => exact repair12276Cell41
  | ⟨42,_⟩ => exact repair12276Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12276 : FrameRepair 12276 scalarRow12276 where
  cap := cap12276
  cap_nonneg := fun j => (repair12276Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12276])
  endpoint := fun j => (repair12276Cells j).2.1
  endpoint_upper := fun j => (repair12276Cells j).2.2.1
  frame := fun j => (repair12276Cells j).2.2.2

noncomputable def cap12277 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34493599 / 125000000 : ℝ)
  | ⟨1,_⟩ => (138175863 / 500000000 : ℝ)
  | ⟨2,_⟩ => (55350733 / 200000000 : ℝ)
  | ⟨3,_⟩ => (277154607 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138777279 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277953519 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278351019 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278748013 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (27914403 / 100000000 : ℝ)
  | ⟨9,_⟩ => (11181563 / 40000000 : ℝ)
  | ⟨10,_⟩ => (279933149 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (11213031 / 40000000 : ℝ)
  | ⟨12,_⟩ => (280717923 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281108623 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (35187407 / 125000000 : ℝ)
  | ⟨15,_⟩ => (28188879 / 100000000 : ℝ)
  | ⟨16,_⟩ => (14113869 / 50000000 : ℝ)
  | ⟨17,_⟩ => (282665039 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141525879 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283437549 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (70955603 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284206359 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142294691 / 500000000 : ℝ)
  | ⟨23,_⟩ => (142485497 / 500000000 : ℝ)
  | ⟨24,_⟩ => (1114657 / 3906250 : ℝ)
  | ⟨25,_⟩ => (28573203 / 100000000 : ℝ)
  | ⟨26,_⟩ => (286111463 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (35811187 / 125000000 : ℝ)
  | ⟨28,_⟩ => (286866633 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143621437 / 500000000 : ℝ)
  | ⟨30,_⟩ => (287617721 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287992183 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (57673153 / 200000000 : ℝ)
  | ⟨33,_⟩ => (72184489 / 250000000 : ℝ)
  | ⟨34,_⟩ => (36138659 / 125000000 : ℝ)
  | ⟨35,_⟩ => (72369929 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289849283 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (29021799 / 100000000 : ℝ)
  | ⟨38,_⟩ => (36323229 / 125000000 : ℝ)
  | ⟨39,_⟩ => (145476151 / 500000000 : ℝ)
  | ⟨40,_⟩ => (36414739 / 125000000 : ℝ)
  | ⟨41,_⟩ => (291682671 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146023289 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12277Cell0 :
    0 ≤ cap12277 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨0,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12277 ⟨0,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨0,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell1 :
    0 ≤ cap12277 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨1,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12277 ⟨1,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨1,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell2 :
    0 ≤ cap12277 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨2,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12277 ⟨2,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨2,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell3 :
    0 ≤ cap12277 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨3,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12277 ⟨3,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨3,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell4 :
    0 ≤ cap12277 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨4,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12277 ⟨4,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨4,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell5 :
    0 ≤ cap12277 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨5,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12277 ⟨5,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨5,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell6 :
    0 ≤ cap12277 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨6,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12277 ⟨6,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨6,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell7 :
    0 ≤ cap12277 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨7,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12277 ⟨7,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨7,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell8 :
    0 ≤ cap12277 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨8,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12277 ⟨8,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨8,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell9 :
    0 ≤ cap12277 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨9,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12277 ⟨9,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨9,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell10 :
    0 ≤ cap12277 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨10,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12277 ⟨10,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨10,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell11 :
    0 ≤ cap12277 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨11,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12277 ⟨11,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨11,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell12 :
    0 ≤ cap12277 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨12,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12277 ⟨12,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨12,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell13 :
    0 ≤ cap12277 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨13,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12277 ⟨13,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨13,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell14 :
    0 ≤ cap12277 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨14,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12277 ⟨14,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨14,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell15 :
    0 ≤ cap12277 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨15,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12277 ⟨15,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨15,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell16 :
    0 ≤ cap12277 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨16,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12277 ⟨16,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨16,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell17 :
    0 ≤ cap12277 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨17,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12277 ⟨17,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨17,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell18 :
    0 ≤ cap12277 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨18,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12277 ⟨18,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨18,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell19 :
    0 ≤ cap12277 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨19,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12277 ⟨19,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨19,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell20 :
    0 ≤ cap12277 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨20,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12277 ⟨20,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨20,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell21 :
    0 ≤ cap12277 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨21,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12277 ⟨21,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨21,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell22 :
    0 ≤ cap12277 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨22,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12277 ⟨22,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨22,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell23 :
    0 ≤ cap12277 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨23,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12277 ⟨23,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨23,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell24 :
    0 ≤ cap12277 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨24,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12277 ⟨24,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨24,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell25 :
    0 ≤ cap12277 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨25,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12277 ⟨25,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨25,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell26 :
    0 ≤ cap12277 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨26,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12277 ⟨26,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨26,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell27 :
    0 ≤ cap12277 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨27,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12277 ⟨27,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨27,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell28 :
    0 ≤ cap12277 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨28,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12277 ⟨28,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨28,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell29 :
    0 ≤ cap12277 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨29,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12277 ⟨29,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨29,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell30 :
    0 ≤ cap12277 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨30,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12277 ⟨30,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨30,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell31 :
    0 ≤ cap12277 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨31,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12277 ⟨31,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨31,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell32 :
    0 ≤ cap12277 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨32,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12277 ⟨32,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨32,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell33 :
    0 ≤ cap12277 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨33,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12277 ⟨33,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨33,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell34 :
    0 ≤ cap12277 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨34,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12277 ⟨34,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨34,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell35 :
    0 ≤ cap12277 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨35,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12277 ⟨35,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨35,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell36 :
    0 ≤ cap12277 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨36,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12277 ⟨36,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨36,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell37 :
    0 ≤ cap12277 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨37,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12277 ⟨37,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨37,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell38 :
    0 ≤ cap12277 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨38,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12277 ⟨38,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨38,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell39 :
    0 ≤ cap12277 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨39,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12277 ⟨39,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨39,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell40 :
    0 ≤ cap12277 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨40,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12277 ⟨40,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨40,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell41 :
    0 ≤ cap12277 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨41,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12277 ⟨41,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨41,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cell42 :
    0 ≤ cap12277 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12277 (parameters ⟨42,by decide⟩)
      (scalarRow12277.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12277 ⟨42,by decide⟩ ∧
    (scalarRow12277.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 ⟨42,by decide⟩ + (scalarRow12277.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12277.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12277.targetFrame := by
  norm_num [cap12277, scalarRow12277, sourceIndex, cell12277, BstLean.Part263.envelope, parameters]

theorem repair12277Cells (j : Fin 43) :
    0 ≤ cap12277 j ∧
    BstLean.Part263.envelope 12277 (parameters j) (scalarRow12277.table (sourceIndex j)).upper ≤ cap12277 j ∧
    (scalarRow12277.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12277 j + (scalarRow12277.table (sourceIndex j)).centre) /
      (scalarRow12277.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12277.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12277Cell0
  | ⟨1,_⟩ => exact repair12277Cell1
  | ⟨2,_⟩ => exact repair12277Cell2
  | ⟨3,_⟩ => exact repair12277Cell3
  | ⟨4,_⟩ => exact repair12277Cell4
  | ⟨5,_⟩ => exact repair12277Cell5
  | ⟨6,_⟩ => exact repair12277Cell6
  | ⟨7,_⟩ => exact repair12277Cell7
  | ⟨8,_⟩ => exact repair12277Cell8
  | ⟨9,_⟩ => exact repair12277Cell9
  | ⟨10,_⟩ => exact repair12277Cell10
  | ⟨11,_⟩ => exact repair12277Cell11
  | ⟨12,_⟩ => exact repair12277Cell12
  | ⟨13,_⟩ => exact repair12277Cell13
  | ⟨14,_⟩ => exact repair12277Cell14
  | ⟨15,_⟩ => exact repair12277Cell15
  | ⟨16,_⟩ => exact repair12277Cell16
  | ⟨17,_⟩ => exact repair12277Cell17
  | ⟨18,_⟩ => exact repair12277Cell18
  | ⟨19,_⟩ => exact repair12277Cell19
  | ⟨20,_⟩ => exact repair12277Cell20
  | ⟨21,_⟩ => exact repair12277Cell21
  | ⟨22,_⟩ => exact repair12277Cell22
  | ⟨23,_⟩ => exact repair12277Cell23
  | ⟨24,_⟩ => exact repair12277Cell24
  | ⟨25,_⟩ => exact repair12277Cell25
  | ⟨26,_⟩ => exact repair12277Cell26
  | ⟨27,_⟩ => exact repair12277Cell27
  | ⟨28,_⟩ => exact repair12277Cell28
  | ⟨29,_⟩ => exact repair12277Cell29
  | ⟨30,_⟩ => exact repair12277Cell30
  | ⟨31,_⟩ => exact repair12277Cell31
  | ⟨32,_⟩ => exact repair12277Cell32
  | ⟨33,_⟩ => exact repair12277Cell33
  | ⟨34,_⟩ => exact repair12277Cell34
  | ⟨35,_⟩ => exact repair12277Cell35
  | ⟨36,_⟩ => exact repair12277Cell36
  | ⟨37,_⟩ => exact repair12277Cell37
  | ⟨38,_⟩ => exact repair12277Cell38
  | ⟨39,_⟩ => exact repair12277Cell39
  | ⟨40,_⟩ => exact repair12277Cell40
  | ⟨41,_⟩ => exact repair12277Cell41
  | ⟨42,_⟩ => exact repair12277Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12277 : FrameRepair 12277 scalarRow12277 where
  cap := cap12277
  cap_nonneg := fun j => (repair12277Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12277])
  endpoint := fun j => (repair12277Cells j).2.1
  endpoint_upper := fun j => (repair12277Cells j).2.2.1
  frame := fun j => (repair12277Cells j).2.2.2

noncomputable def cap12278 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275948717 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (69087911 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276753577 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (17322157 / 62500000 : ℝ)
  | ⟨4,_⟩ => (277554457 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277953411 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55670181 / 200000000 : ℝ)
  | ⟨7,_⟩ => (69686973 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279143903 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139769471 / 500000000 : ℝ)
  | ⟨10,_⟩ => (27993301 / 100000000 : ℝ)
  | ⟨11,_⟩ => (280325629 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (28071777 / 100000000 : ℝ)
  | ⟨13,_⟩ => (17569279 / 62500000 : ℝ)
  | ⟨14,_⟩ => (281499091 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140944309 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141138601 / 500000000 : ℝ)
  | ⟨17,_⟩ => (56532971 / 200000000 : ℝ)
  | ⟨18,_⟩ => (17690723 / 62500000 : ℝ)
  | ⟨19,_⟩ => (283437353 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (28382221 / 100000000 : ℝ)
  | ⟨21,_⟩ => (5684123 / 20000000 : ℝ)
  | ⟨22,_⟩ => (284589167 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (71242693 / 250000000 : ℝ)
  | ⟨24,_⟩ => (57070393 / 200000000 : ℝ)
  | ⟨25,_⟩ => (71432949 / 250000000 : ℝ)
  | ⟨26,_⟩ => (286111223 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (1145957 / 4000000 : ℝ)
  | ⟨28,_⟩ => (286866381 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (35905327 / 125000000 : ℝ)
  | ⟨30,_⟩ => (287617457 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287991913 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288365489 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144368837 / 500000000 : ℝ)
  | ⟨34,_⟩ => (289108983 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289479421 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144924491 / 500000000 : ℝ)
  | ⟨37,_⟩ => (72554421 / 250000000 : ℝ)
  | ⟨38,_⟩ => (3632319 / 12500000 : ℝ)
  | ⟨39,_⟩ => (290951983 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (72829397 / 250000000 : ℝ)
  | ⟨41,_⟩ => (291682341 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146023121 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12278Cell0 :
    0 ≤ cap12278 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨0,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12278 ⟨0,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨0,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell1 :
    0 ≤ cap12278 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨1,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12278 ⟨1,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨1,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell2 :
    0 ≤ cap12278 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨2,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12278 ⟨2,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨2,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell3 :
    0 ≤ cap12278 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨3,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12278 ⟨3,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨3,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell4 :
    0 ≤ cap12278 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨4,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12278 ⟨4,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨4,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell5 :
    0 ≤ cap12278 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨5,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12278 ⟨5,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨5,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell6 :
    0 ≤ cap12278 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨6,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12278 ⟨6,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨6,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell7 :
    0 ≤ cap12278 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨7,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12278 ⟨7,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨7,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell8 :
    0 ≤ cap12278 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨8,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12278 ⟨8,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨8,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell9 :
    0 ≤ cap12278 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨9,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12278 ⟨9,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨9,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell10 :
    0 ≤ cap12278 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨10,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12278 ⟨10,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨10,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell11 :
    0 ≤ cap12278 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨11,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12278 ⟨11,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨11,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell12 :
    0 ≤ cap12278 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨12,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12278 ⟨12,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨12,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell13 :
    0 ≤ cap12278 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨13,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12278 ⟨13,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨13,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell14 :
    0 ≤ cap12278 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨14,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12278 ⟨14,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨14,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell15 :
    0 ≤ cap12278 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨15,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12278 ⟨15,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨15,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell16 :
    0 ≤ cap12278 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨16,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12278 ⟨16,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨16,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell17 :
    0 ≤ cap12278 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨17,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12278 ⟨17,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨17,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell18 :
    0 ≤ cap12278 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨18,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12278 ⟨18,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨18,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell19 :
    0 ≤ cap12278 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨19,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12278 ⟨19,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨19,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell20 :
    0 ≤ cap12278 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨20,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12278 ⟨20,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨20,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell21 :
    0 ≤ cap12278 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨21,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12278 ⟨21,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨21,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell22 :
    0 ≤ cap12278 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨22,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12278 ⟨22,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨22,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell23 :
    0 ≤ cap12278 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨23,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12278 ⟨23,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨23,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell24 :
    0 ≤ cap12278 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨24,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12278 ⟨24,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨24,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell25 :
    0 ≤ cap12278 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨25,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12278 ⟨25,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨25,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell26 :
    0 ≤ cap12278 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨26,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12278 ⟨26,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨26,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell27 :
    0 ≤ cap12278 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨27,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12278 ⟨27,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨27,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell28 :
    0 ≤ cap12278 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨28,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12278 ⟨28,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨28,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell29 :
    0 ≤ cap12278 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨29,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12278 ⟨29,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨29,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell30 :
    0 ≤ cap12278 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨30,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12278 ⟨30,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨30,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell31 :
    0 ≤ cap12278 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨31,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12278 ⟨31,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨31,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell32 :
    0 ≤ cap12278 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨32,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12278 ⟨32,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨32,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell33 :
    0 ≤ cap12278 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨33,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12278 ⟨33,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨33,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell34 :
    0 ≤ cap12278 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨34,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12278 ⟨34,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨34,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell35 :
    0 ≤ cap12278 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨35,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12278 ⟨35,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨35,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell36 :
    0 ≤ cap12278 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨36,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12278 ⟨36,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨36,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell37 :
    0 ≤ cap12278 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨37,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12278 ⟨37,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨37,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell38 :
    0 ≤ cap12278 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨38,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12278 ⟨38,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨38,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell39 :
    0 ≤ cap12278 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨39,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12278 ⟨39,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨39,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell40 :
    0 ≤ cap12278 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨40,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12278 ⟨40,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨40,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell41 :
    0 ≤ cap12278 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨41,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12278 ⟨41,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨41,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cell42 :
    0 ≤ cap12278 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12278 (parameters ⟨42,by decide⟩)
      (scalarRow12278.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12278 ⟨42,by decide⟩ ∧
    (scalarRow12278.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 ⟨42,by decide⟩ + (scalarRow12278.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12278.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12278.targetFrame := by
  norm_num [cap12278, scalarRow12278, sourceIndex, cell12278, BstLean.Part263.envelope, parameters]

theorem repair12278Cells (j : Fin 43) :
    0 ≤ cap12278 j ∧
    BstLean.Part263.envelope 12278 (parameters j) (scalarRow12278.table (sourceIndex j)).upper ≤ cap12278 j ∧
    (scalarRow12278.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12278 j + (scalarRow12278.table (sourceIndex j)).centre) /
      (scalarRow12278.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12278.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12278Cell0
  | ⟨1,_⟩ => exact repair12278Cell1
  | ⟨2,_⟩ => exact repair12278Cell2
  | ⟨3,_⟩ => exact repair12278Cell3
  | ⟨4,_⟩ => exact repair12278Cell4
  | ⟨5,_⟩ => exact repair12278Cell5
  | ⟨6,_⟩ => exact repair12278Cell6
  | ⟨7,_⟩ => exact repair12278Cell7
  | ⟨8,_⟩ => exact repair12278Cell8
  | ⟨9,_⟩ => exact repair12278Cell9
  | ⟨10,_⟩ => exact repair12278Cell10
  | ⟨11,_⟩ => exact repair12278Cell11
  | ⟨12,_⟩ => exact repair12278Cell12
  | ⟨13,_⟩ => exact repair12278Cell13
  | ⟨14,_⟩ => exact repair12278Cell14
  | ⟨15,_⟩ => exact repair12278Cell15
  | ⟨16,_⟩ => exact repair12278Cell16
  | ⟨17,_⟩ => exact repair12278Cell17
  | ⟨18,_⟩ => exact repair12278Cell18
  | ⟨19,_⟩ => exact repair12278Cell19
  | ⟨20,_⟩ => exact repair12278Cell20
  | ⟨21,_⟩ => exact repair12278Cell21
  | ⟨22,_⟩ => exact repair12278Cell22
  | ⟨23,_⟩ => exact repair12278Cell23
  | ⟨24,_⟩ => exact repair12278Cell24
  | ⟨25,_⟩ => exact repair12278Cell25
  | ⟨26,_⟩ => exact repair12278Cell26
  | ⟨27,_⟩ => exact repair12278Cell27
  | ⟨28,_⟩ => exact repair12278Cell28
  | ⟨29,_⟩ => exact repair12278Cell29
  | ⟨30,_⟩ => exact repair12278Cell30
  | ⟨31,_⟩ => exact repair12278Cell31
  | ⟨32,_⟩ => exact repair12278Cell32
  | ⟨33,_⟩ => exact repair12278Cell33
  | ⟨34,_⟩ => exact repair12278Cell34
  | ⟨35,_⟩ => exact repair12278Cell35
  | ⟨36,_⟩ => exact repair12278Cell36
  | ⟨37,_⟩ => exact repair12278Cell37
  | ⟨38,_⟩ => exact repair12278Cell38
  | ⟨39,_⟩ => exact repair12278Cell39
  | ⟨40,_⟩ => exact repair12278Cell40
  | ⟨41,_⟩ => exact repair12278Cell41
  | ⟨42,_⟩ => exact repair12278Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12278 : FrameRepair 12278 scalarRow12278 where
  cap := cap12278
  cap_nonneg := fun j => (repair12278Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12278])
  endpoint := fun j => (repair12278Cells j).2.1
  endpoint_upper := fun j => (repair12278Cells j).2.2.1
  frame := fun j => (repair12278Cells j).2.2.2

noncomputable def cap12279 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275948641 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138175781 / 500000000 : ℝ)
  | ⟨2,_⟩ => (17297093 / 62500000 : ℝ)
  | ⟨3,_⟩ => (277154417 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (55510871 / 200000000 : ℝ)
  | ⟨5,_⟩ => (277953303 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (27835079 / 100000000 : ℝ)
  | ⟨7,_⟩ => (278747771 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (8723243 / 31250000 : ℝ)
  | ⟨9,_⟩ => (279538809 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (27993287 / 100000000 : ℝ)
  | ⟨11,_⟩ => (280325483 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140358809 / 500000000 : ℝ)
  | ⟨13,_⟩ => (140554153 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140749463 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281888447 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (11291081 / 40000000 : ℝ)
  | ⟨17,_⟩ => (282664671 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141525689 / 500000000 : ℝ)
  | ⟨19,_⟩ => (70859289 / 250000000 : ℝ)
  | ⟨20,_⟩ => (283822007 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (142102971 / 500000000 : ℝ)
  | ⟨22,_⟩ => (35573619 / 125000000 : ℝ)
  | ⟨23,_⟩ => (284970551 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142675869 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285731563 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (35763873 / 125000000 : ℝ)
  | ⟨27,_⟩ => (57297801 / 200000000 : ℝ)
  | ⟨28,_⟩ => (286866129 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143621179 / 500000000 : ℝ)
  | ⟨30,_⟩ => (35952149 / 125000000 : ℝ)
  | ⟨31,_⟩ => (287991643 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72091303 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288737391 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (57821739 / 200000000 : ℝ)
  | ⟨35,_⟩ => (289479127 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144924341 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290217377 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290585207 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (58190333 / 200000000 : ℝ)
  | ⟨40,_⟩ => (291317263 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (29168201 / 100000000 : ℝ)
  | ⟨42,_⟩ => (58409181 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12279Cell0 :
    0 ≤ cap12279 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨0,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12279 ⟨0,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨0,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell1 :
    0 ≤ cap12279 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨1,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12279 ⟨1,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨1,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell2 :
    0 ≤ cap12279 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨2,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12279 ⟨2,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨2,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell3 :
    0 ≤ cap12279 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨3,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12279 ⟨3,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨3,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell4 :
    0 ≤ cap12279 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨4,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12279 ⟨4,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨4,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell5 :
    0 ≤ cap12279 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨5,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12279 ⟨5,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨5,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell6 :
    0 ≤ cap12279 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨6,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12279 ⟨6,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨6,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell7 :
    0 ≤ cap12279 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨7,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12279 ⟨7,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨7,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell8 :
    0 ≤ cap12279 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨8,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12279 ⟨8,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨8,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell9 :
    0 ≤ cap12279 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨9,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12279 ⟨9,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨9,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell10 :
    0 ≤ cap12279 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨10,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12279 ⟨10,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨10,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell11 :
    0 ≤ cap12279 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨11,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12279 ⟨11,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨11,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell12 :
    0 ≤ cap12279 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨12,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12279 ⟨12,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨12,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell13 :
    0 ≤ cap12279 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨13,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12279 ⟨13,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨13,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell14 :
    0 ≤ cap12279 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨14,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12279 ⟨14,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨14,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell15 :
    0 ≤ cap12279 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨15,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12279 ⟨15,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨15,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell16 :
    0 ≤ cap12279 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨16,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12279 ⟨16,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨16,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell17 :
    0 ≤ cap12279 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨17,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12279 ⟨17,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨17,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell18 :
    0 ≤ cap12279 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨18,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12279 ⟨18,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨18,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell19 :
    0 ≤ cap12279 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨19,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12279 ⟨19,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨19,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell20 :
    0 ≤ cap12279 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨20,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12279 ⟨20,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨20,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell21 :
    0 ≤ cap12279 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨21,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12279 ⟨21,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨21,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell22 :
    0 ≤ cap12279 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨22,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12279 ⟨22,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨22,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell23 :
    0 ≤ cap12279 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨23,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12279 ⟨23,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨23,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell24 :
    0 ≤ cap12279 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨24,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12279 ⟨24,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨24,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell25 :
    0 ≤ cap12279 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨25,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12279 ⟨25,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨25,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell26 :
    0 ≤ cap12279 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨26,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12279 ⟨26,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨26,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell27 :
    0 ≤ cap12279 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨27,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12279 ⟨27,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨27,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell28 :
    0 ≤ cap12279 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨28,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12279 ⟨28,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨28,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell29 :
    0 ≤ cap12279 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨29,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12279 ⟨29,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨29,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell30 :
    0 ≤ cap12279 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨30,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12279 ⟨30,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨30,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell31 :
    0 ≤ cap12279 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨31,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12279 ⟨31,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨31,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell32 :
    0 ≤ cap12279 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨32,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12279 ⟨32,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨32,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell33 :
    0 ≤ cap12279 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨33,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12279 ⟨33,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨33,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell34 :
    0 ≤ cap12279 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨34,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12279 ⟨34,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨34,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell35 :
    0 ≤ cap12279 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨35,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12279 ⟨35,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨35,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell36 :
    0 ≤ cap12279 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨36,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12279 ⟨36,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨36,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell37 :
    0 ≤ cap12279 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨37,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12279 ⟨37,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨37,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell38 :
    0 ≤ cap12279 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨38,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12279 ⟨38,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨38,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell39 :
    0 ≤ cap12279 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨39,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12279 ⟨39,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨39,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell40 :
    0 ≤ cap12279 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨40,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12279 ⟨40,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨40,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell41 :
    0 ≤ cap12279 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨41,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12279 ⟨41,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨41,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cell42 :
    0 ≤ cap12279 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12279 (parameters ⟨42,by decide⟩)
      (scalarRow12279.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12279 ⟨42,by decide⟩ ∧
    (scalarRow12279.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 ⟨42,by decide⟩ + (scalarRow12279.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12279.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12279.targetFrame := by
  norm_num [cap12279, scalarRow12279, sourceIndex, cell12279, BstLean.Part263.envelope, parameters]

theorem repair12279Cells (j : Fin 43) :
    0 ≤ cap12279 j ∧
    BstLean.Part263.envelope 12279 (parameters j) (scalarRow12279.table (sourceIndex j)).upper ≤ cap12279 j ∧
    (scalarRow12279.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12279 j + (scalarRow12279.table (sourceIndex j)).centre) /
      (scalarRow12279.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12279.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12279Cell0
  | ⟨1,_⟩ => exact repair12279Cell1
  | ⟨2,_⟩ => exact repair12279Cell2
  | ⟨3,_⟩ => exact repair12279Cell3
  | ⟨4,_⟩ => exact repair12279Cell4
  | ⟨5,_⟩ => exact repair12279Cell5
  | ⟨6,_⟩ => exact repair12279Cell6
  | ⟨7,_⟩ => exact repair12279Cell7
  | ⟨8,_⟩ => exact repair12279Cell8
  | ⟨9,_⟩ => exact repair12279Cell9
  | ⟨10,_⟩ => exact repair12279Cell10
  | ⟨11,_⟩ => exact repair12279Cell11
  | ⟨12,_⟩ => exact repair12279Cell12
  | ⟨13,_⟩ => exact repair12279Cell13
  | ⟨14,_⟩ => exact repair12279Cell14
  | ⟨15,_⟩ => exact repair12279Cell15
  | ⟨16,_⟩ => exact repair12279Cell16
  | ⟨17,_⟩ => exact repair12279Cell17
  | ⟨18,_⟩ => exact repair12279Cell18
  | ⟨19,_⟩ => exact repair12279Cell19
  | ⟨20,_⟩ => exact repair12279Cell20
  | ⟨21,_⟩ => exact repair12279Cell21
  | ⟨22,_⟩ => exact repair12279Cell22
  | ⟨23,_⟩ => exact repair12279Cell23
  | ⟨24,_⟩ => exact repair12279Cell24
  | ⟨25,_⟩ => exact repair12279Cell25
  | ⟨26,_⟩ => exact repair12279Cell26
  | ⟨27,_⟩ => exact repair12279Cell27
  | ⟨28,_⟩ => exact repair12279Cell28
  | ⟨29,_⟩ => exact repair12279Cell29
  | ⟨30,_⟩ => exact repair12279Cell30
  | ⟨31,_⟩ => exact repair12279Cell31
  | ⟨32,_⟩ => exact repair12279Cell32
  | ⟨33,_⟩ => exact repair12279Cell33
  | ⟨34,_⟩ => exact repair12279Cell34
  | ⟨35,_⟩ => exact repair12279Cell35
  | ⟨36,_⟩ => exact repair12279Cell36
  | ⟨37,_⟩ => exact repair12279Cell37
  | ⟨38,_⟩ => exact repair12279Cell38
  | ⟨39,_⟩ => exact repair12279Cell39
  | ⟨40,_⟩ => exact repair12279Cell40
  | ⟨41,_⟩ => exact repair12279Cell41
  | ⟨42,_⟩ => exact repair12279Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12279 : FrameRepair 12279 scalarRow12279 where
  cap := cap12279
  cap_nonneg := fun j => (repair12279Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12279])
  endpoint := fun j => (repair12279Cells j).2.1
  endpoint_upper := fun j => (repair12279Cells j).2.2.1
  frame := fun j => (repair12279Cells j).2.2.2

noncomputable def cap12280 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137974283 / 500000000 : ℝ)
  | ⟨1,_⟩ => (6908787 / 25000000 : ℝ)
  | ⟨2,_⟩ => (1383767 / 5000000 : ℝ)
  | ⟨3,_⟩ => (138577161 / 500000000 : ℝ)
  | ⟨4,_⟩ => (138777127 / 500000000 : ℝ)
  | ⟨5,_⟩ => (69488299 / 250000000 : ℝ)
  | ⟨6,_⟩ => (69587669 / 250000000 : ℝ)
  | ⟨7,_⟩ => (278747651 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279143649 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (11181547 / 40000000 : ℝ)
  | ⟨10,_⟩ => (27993273 / 100000000 : ℝ)
  | ⟨11,_⟩ => (280325337 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (56143493 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281108147 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281498761 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70472069 / 250000000 : ℝ)
  | ⟨16,_⟩ => (282276847 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282664487 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (70762797 / 250000000 : ℝ)
  | ⟨19,_⟩ => (1771481 / 6250000 : ℝ)
  | ⟨20,_⟩ => (56764361 / 200000000 : ℝ)
  | ⟨21,_⟩ => (284205733 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284588737 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (28497033 / 100000000 : ℝ)
  | ⟨24,_⟩ => (28535151 / 100000000 : ℝ)
  | ⟨25,_⟩ => (285731329 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (35763843 / 125000000 : ℝ)
  | ⟨27,_⟩ => (286488759 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286865877 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (2872421 / 10000000 : ℝ)
  | ⟨30,_⟩ => (8988029 / 31250000 : ℝ)
  | ⟨31,_⟩ => (287991373 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (36045617 / 125000000 : ℝ)
  | ⟨33,_⟩ => (288737109 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144554203 / 500000000 : ℝ)
  | ⟨35,_⟩ => (18092427 / 62500000 : ℝ)
  | ⟨36,_⟩ => (289848381 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290217071 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (58116979 / 200000000 : ℝ)
  | ⟨39,_⟩ => (145475673 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291316939 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (3646021 / 12500000 : ℝ)
  | ⟨42,_⟩ => (292045569 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12280Cell0 :
    0 ≤ cap12280 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨0,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12280 ⟨0,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨0,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell1 :
    0 ≤ cap12280 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨1,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12280 ⟨1,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨1,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell2 :
    0 ≤ cap12280 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨2,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12280 ⟨2,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨2,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell3 :
    0 ≤ cap12280 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨3,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12280 ⟨3,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨3,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell4 :
    0 ≤ cap12280 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨4,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12280 ⟨4,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨4,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell5 :
    0 ≤ cap12280 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨5,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12280 ⟨5,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨5,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell6 :
    0 ≤ cap12280 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨6,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12280 ⟨6,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨6,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell7 :
    0 ≤ cap12280 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨7,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12280 ⟨7,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨7,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell8 :
    0 ≤ cap12280 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨8,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12280 ⟨8,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨8,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell9 :
    0 ≤ cap12280 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨9,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12280 ⟨9,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨9,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell10 :
    0 ≤ cap12280 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨10,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12280 ⟨10,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨10,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell11 :
    0 ≤ cap12280 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨11,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12280 ⟨11,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨11,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell12 :
    0 ≤ cap12280 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨12,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12280 ⟨12,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨12,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell13 :
    0 ≤ cap12280 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨13,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12280 ⟨13,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨13,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell14 :
    0 ≤ cap12280 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨14,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12280 ⟨14,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨14,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell15 :
    0 ≤ cap12280 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨15,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12280 ⟨15,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨15,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell16 :
    0 ≤ cap12280 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨16,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12280 ⟨16,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨16,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell17 :
    0 ≤ cap12280 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨17,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12280 ⟨17,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨17,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell18 :
    0 ≤ cap12280 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨18,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12280 ⟨18,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨18,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell19 :
    0 ≤ cap12280 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨19,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12280 ⟨19,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨19,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell20 :
    0 ≤ cap12280 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨20,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12280 ⟨20,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨20,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell21 :
    0 ≤ cap12280 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨21,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12280 ⟨21,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨21,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell22 :
    0 ≤ cap12280 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨22,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12280 ⟨22,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨22,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell23 :
    0 ≤ cap12280 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨23,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12280 ⟨23,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨23,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell24 :
    0 ≤ cap12280 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨24,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12280 ⟨24,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨24,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell25 :
    0 ≤ cap12280 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨25,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12280 ⟨25,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨25,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell26 :
    0 ≤ cap12280 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨26,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12280 ⟨26,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨26,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell27 :
    0 ≤ cap12280 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨27,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12280 ⟨27,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨27,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell28 :
    0 ≤ cap12280 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨28,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12280 ⟨28,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨28,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell29 :
    0 ≤ cap12280 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨29,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12280 ⟨29,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨29,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell30 :
    0 ≤ cap12280 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨30,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12280 ⟨30,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨30,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell31 :
    0 ≤ cap12280 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨31,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12280 ⟨31,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨31,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell32 :
    0 ≤ cap12280 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨32,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12280 ⟨32,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨32,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell33 :
    0 ≤ cap12280 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨33,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12280 ⟨33,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨33,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell34 :
    0 ≤ cap12280 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨34,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12280 ⟨34,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨34,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell35 :
    0 ≤ cap12280 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨35,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12280 ⟨35,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨35,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell36 :
    0 ≤ cap12280 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨36,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12280 ⟨36,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨36,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell37 :
    0 ≤ cap12280 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨37,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12280 ⟨37,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨37,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell38 :
    0 ≤ cap12280 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨38,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12280 ⟨38,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨38,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell39 :
    0 ≤ cap12280 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨39,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12280 ⟨39,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨39,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell40 :
    0 ≤ cap12280 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨40,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12280 ⟨40,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨40,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell41 :
    0 ≤ cap12280 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨41,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12280 ⟨41,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨41,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cell42 :
    0 ≤ cap12280 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12280 (parameters ⟨42,by decide⟩)
      (scalarRow12280.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12280 ⟨42,by decide⟩ ∧
    (scalarRow12280.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 ⟨42,by decide⟩ + (scalarRow12280.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12280.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12280.targetFrame := by
  norm_num [cap12280, scalarRow12280, sourceIndex, cell12280, BstLean.Part263.envelope, parameters]

theorem repair12280Cells (j : Fin 43) :
    0 ≤ cap12280 j ∧
    BstLean.Part263.envelope 12280 (parameters j) (scalarRow12280.table (sourceIndex j)).upper ≤ cap12280 j ∧
    (scalarRow12280.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12280 j + (scalarRow12280.table (sourceIndex j)).centre) /
      (scalarRow12280.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12280.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12280Cell0
  | ⟨1,_⟩ => exact repair12280Cell1
  | ⟨2,_⟩ => exact repair12280Cell2
  | ⟨3,_⟩ => exact repair12280Cell3
  | ⟨4,_⟩ => exact repair12280Cell4
  | ⟨5,_⟩ => exact repair12280Cell5
  | ⟨6,_⟩ => exact repair12280Cell6
  | ⟨7,_⟩ => exact repair12280Cell7
  | ⟨8,_⟩ => exact repair12280Cell8
  | ⟨9,_⟩ => exact repair12280Cell9
  | ⟨10,_⟩ => exact repair12280Cell10
  | ⟨11,_⟩ => exact repair12280Cell11
  | ⟨12,_⟩ => exact repair12280Cell12
  | ⟨13,_⟩ => exact repair12280Cell13
  | ⟨14,_⟩ => exact repair12280Cell14
  | ⟨15,_⟩ => exact repair12280Cell15
  | ⟨16,_⟩ => exact repair12280Cell16
  | ⟨17,_⟩ => exact repair12280Cell17
  | ⟨18,_⟩ => exact repair12280Cell18
  | ⟨19,_⟩ => exact repair12280Cell19
  | ⟨20,_⟩ => exact repair12280Cell20
  | ⟨21,_⟩ => exact repair12280Cell21
  | ⟨22,_⟩ => exact repair12280Cell22
  | ⟨23,_⟩ => exact repair12280Cell23
  | ⟨24,_⟩ => exact repair12280Cell24
  | ⟨25,_⟩ => exact repair12280Cell25
  | ⟨26,_⟩ => exact repair12280Cell26
  | ⟨27,_⟩ => exact repair12280Cell27
  | ⟨28,_⟩ => exact repair12280Cell28
  | ⟨29,_⟩ => exact repair12280Cell29
  | ⟨30,_⟩ => exact repair12280Cell30
  | ⟨31,_⟩ => exact repair12280Cell31
  | ⟨32,_⟩ => exact repair12280Cell32
  | ⟨33,_⟩ => exact repair12280Cell33
  | ⟨34,_⟩ => exact repair12280Cell34
  | ⟨35,_⟩ => exact repair12280Cell35
  | ⟨36,_⟩ => exact repair12280Cell36
  | ⟨37,_⟩ => exact repair12280Cell37
  | ⟨38,_⟩ => exact repair12280Cell38
  | ⟨39,_⟩ => exact repair12280Cell39
  | ⟨40,_⟩ => exact repair12280Cell40
  | ⟨41,_⟩ => exact repair12280Cell41
  | ⟨42,_⟩ => exact repair12280Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12280 : FrameRepair 12280 scalarRow12280 where
  cap := cap12280
  cap_nonneg := fun j => (repair12280Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12280])
  endpoint := fun j => (repair12280Cells j).2.1
  endpoint_upper := fun j => (repair12280Cells j).2.2.1
  frame := fun j => (repair12280Cells j).2.2.2

noncomputable def cap12281 : Fin 43 → ℝ
  | ⟨0,_⟩ => (27594849 / 100000000 : ℝ)
  | ⟨1,_⟩ => (138175699 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276753311 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277154227 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (34694269 / 125000000 : ℝ)
  | ⟨5,_⟩ => (4343017 / 15625000 : ℝ)
  | ⟨6,_⟩ => (139175281 / 500000000 : ℝ)
  | ⟨7,_⟩ => (27874753 / 100000000 : ℝ)
  | ⟨8,_⟩ => (139571761 / 500000000 : ℝ)
  | ⟨9,_⟩ => (139769271 / 500000000 : ℝ)
  | ⟨10,_⟩ => (27993259 / 100000000 : ℝ)
  | ⟨11,_⟩ => (280325191 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280717313 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70276997 / 250000000 : ℝ)
  | ⟨14,_⟩ => (70374649 / 250000000 : ℝ)
  | ⟨15,_⟩ => (35236013 / 125000000 : ℝ)
  | ⟨16,_⟩ => (28227667 / 100000000 : ℝ)
  | ⟨17,_⟩ => (282664303 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141525499 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283436763 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141910801 / 500000000 : ℝ)
  | ⟨21,_⟩ => (71051381 / 250000000 : ℝ)
  | ⟨22,_⟩ => (142294261 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284970109 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285351283 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (35716387 / 125000000 : ℝ)
  | ⟨26,_⟩ => (35763813 / 125000000 : ℝ)
  | ⟨27,_⟩ => (286488513 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (91797 / 320000 : ℝ)
  | ⟨29,_⟩ => (287241841 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (35952083 / 125000000 : ℝ)
  | ⟨31,_⟩ => (143995551 / 500000000 : ℝ)
  | ⟨32,_⟩ => (14418233 / 50000000 : ℝ)
  | ⟨33,_⟩ => (144368413 / 500000000 : ℝ)
  | ⟨34,_⟩ => (144554059 / 500000000 : ℝ)
  | ⟨35,_⟩ => (144739269 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289848081 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (72554191 / 250000000 : ℝ)
  | ⟨38,_⟩ => (145292291 / 500000000 : ℝ)
  | ⟨39,_⟩ => (72737757 / 250000000 : ℝ)
  | ⟨40,_⟩ => (58263323 / 200000000 : ℝ)
  | ⟨41,_⟩ => (5833627 / 20000000 : ℝ)
  | ⟨42,_⟩ => (292045233 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12281Cell0 :
    0 ≤ cap12281 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨0,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12281 ⟨0,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨0,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell1 :
    0 ≤ cap12281 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨1,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12281 ⟨1,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨1,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell2 :
    0 ≤ cap12281 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨2,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12281 ⟨2,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨2,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell3 :
    0 ≤ cap12281 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨3,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12281 ⟨3,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨3,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell4 :
    0 ≤ cap12281 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨4,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12281 ⟨4,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨4,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell5 :
    0 ≤ cap12281 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨5,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12281 ⟨5,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨5,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell6 :
    0 ≤ cap12281 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨6,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12281 ⟨6,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨6,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell7 :
    0 ≤ cap12281 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨7,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12281 ⟨7,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨7,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell8 :
    0 ≤ cap12281 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨8,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12281 ⟨8,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨8,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell9 :
    0 ≤ cap12281 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨9,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12281 ⟨9,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨9,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell10 :
    0 ≤ cap12281 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨10,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12281 ⟨10,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨10,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell11 :
    0 ≤ cap12281 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨11,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12281 ⟨11,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨11,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell12 :
    0 ≤ cap12281 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨12,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12281 ⟨12,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨12,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell13 :
    0 ≤ cap12281 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨13,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12281 ⟨13,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨13,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell14 :
    0 ≤ cap12281 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨14,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12281 ⟨14,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨14,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell15 :
    0 ≤ cap12281 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨15,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12281 ⟨15,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨15,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell16 :
    0 ≤ cap12281 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨16,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12281 ⟨16,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨16,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell17 :
    0 ≤ cap12281 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨17,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12281 ⟨17,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨17,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell18 :
    0 ≤ cap12281 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨18,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12281 ⟨18,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨18,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell19 :
    0 ≤ cap12281 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨19,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12281 ⟨19,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨19,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell20 :
    0 ≤ cap12281 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨20,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12281 ⟨20,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨20,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell21 :
    0 ≤ cap12281 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨21,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12281 ⟨21,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨21,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell22 :
    0 ≤ cap12281 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨22,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12281 ⟨22,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨22,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell23 :
    0 ≤ cap12281 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨23,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12281 ⟨23,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨23,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell24 :
    0 ≤ cap12281 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨24,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12281 ⟨24,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨24,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell25 :
    0 ≤ cap12281 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨25,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12281 ⟨25,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨25,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell26 :
    0 ≤ cap12281 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨26,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12281 ⟨26,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨26,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell27 :
    0 ≤ cap12281 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨27,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12281 ⟨27,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨27,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell28 :
    0 ≤ cap12281 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨28,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12281 ⟨28,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨28,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell29 :
    0 ≤ cap12281 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨29,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12281 ⟨29,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨29,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell30 :
    0 ≤ cap12281 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨30,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12281 ⟨30,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨30,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell31 :
    0 ≤ cap12281 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨31,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12281 ⟨31,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨31,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell32 :
    0 ≤ cap12281 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨32,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12281 ⟨32,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨32,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell33 :
    0 ≤ cap12281 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨33,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12281 ⟨33,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨33,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell34 :
    0 ≤ cap12281 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨34,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12281 ⟨34,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨34,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell35 :
    0 ≤ cap12281 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨35,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12281 ⟨35,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨35,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell36 :
    0 ≤ cap12281 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨36,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12281 ⟨36,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨36,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell37 :
    0 ≤ cap12281 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨37,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12281 ⟨37,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨37,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell38 :
    0 ≤ cap12281 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨38,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12281 ⟨38,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨38,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell39 :
    0 ≤ cap12281 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨39,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12281 ⟨39,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨39,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell40 :
    0 ≤ cap12281 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨40,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12281 ⟨40,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨40,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell41 :
    0 ≤ cap12281 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨41,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12281 ⟨41,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨41,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cell42 :
    0 ≤ cap12281 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12281 (parameters ⟨42,by decide⟩)
      (scalarRow12281.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12281 ⟨42,by decide⟩ ∧
    (scalarRow12281.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 ⟨42,by decide⟩ + (scalarRow12281.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12281.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12281.targetFrame := by
  norm_num [cap12281, scalarRow12281, sourceIndex, cell12281, BstLean.Part263.envelope, parameters]

theorem repair12281Cells (j : Fin 43) :
    0 ≤ cap12281 j ∧
    BstLean.Part263.envelope 12281 (parameters j) (scalarRow12281.table (sourceIndex j)).upper ≤ cap12281 j ∧
    (scalarRow12281.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12281 j + (scalarRow12281.table (sourceIndex j)).centre) /
      (scalarRow12281.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12281.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12281Cell0
  | ⟨1,_⟩ => exact repair12281Cell1
  | ⟨2,_⟩ => exact repair12281Cell2
  | ⟨3,_⟩ => exact repair12281Cell3
  | ⟨4,_⟩ => exact repair12281Cell4
  | ⟨5,_⟩ => exact repair12281Cell5
  | ⟨6,_⟩ => exact repair12281Cell6
  | ⟨7,_⟩ => exact repair12281Cell7
  | ⟨8,_⟩ => exact repair12281Cell8
  | ⟨9,_⟩ => exact repair12281Cell9
  | ⟨10,_⟩ => exact repair12281Cell10
  | ⟨11,_⟩ => exact repair12281Cell11
  | ⟨12,_⟩ => exact repair12281Cell12
  | ⟨13,_⟩ => exact repair12281Cell13
  | ⟨14,_⟩ => exact repair12281Cell14
  | ⟨15,_⟩ => exact repair12281Cell15
  | ⟨16,_⟩ => exact repair12281Cell16
  | ⟨17,_⟩ => exact repair12281Cell17
  | ⟨18,_⟩ => exact repair12281Cell18
  | ⟨19,_⟩ => exact repair12281Cell19
  | ⟨20,_⟩ => exact repair12281Cell20
  | ⟨21,_⟩ => exact repair12281Cell21
  | ⟨22,_⟩ => exact repair12281Cell22
  | ⟨23,_⟩ => exact repair12281Cell23
  | ⟨24,_⟩ => exact repair12281Cell24
  | ⟨25,_⟩ => exact repair12281Cell25
  | ⟨26,_⟩ => exact repair12281Cell26
  | ⟨27,_⟩ => exact repair12281Cell27
  | ⟨28,_⟩ => exact repair12281Cell28
  | ⟨29,_⟩ => exact repair12281Cell29
  | ⟨30,_⟩ => exact repair12281Cell30
  | ⟨31,_⟩ => exact repair12281Cell31
  | ⟨32,_⟩ => exact repair12281Cell32
  | ⟨33,_⟩ => exact repair12281Cell33
  | ⟨34,_⟩ => exact repair12281Cell34
  | ⟨35,_⟩ => exact repair12281Cell35
  | ⟨36,_⟩ => exact repair12281Cell36
  | ⟨37,_⟩ => exact repair12281Cell37
  | ⟨38,_⟩ => exact repair12281Cell38
  | ⟨39,_⟩ => exact repair12281Cell39
  | ⟨40,_⟩ => exact repair12281Cell40
  | ⟨41,_⟩ => exact repair12281Cell41
  | ⟨42,_⟩ => exact repair12281Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12281 : FrameRepair 12281 scalarRow12281 where
  cap := cap12281
  cap_nonneg := fun j => (repair12281Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12281])
  endpoint := fun j => (repair12281Cells j).2.1
  endpoint_upper := fun j => (repair12281Cells j).2.2.1
  frame := fun j => (repair12281Cells j).2.2.2

noncomputable def cap12282 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55189683 / 200000000 : ℝ)
  | ⟨1,_⟩ => (69087829 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276753223 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (69288533 / 250000000 : ℝ)
  | ⟨4,_⟩ => (277554051 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (13897649 / 50000000 : ℝ)
  | ⟨6,_⟩ => (17396903 / 62500000 : ℝ)
  | ⟨7,_⟩ => (27874741 / 100000000 : ℝ)
  | ⟨8,_⟩ => (55828679 / 200000000 : ℝ)
  | ⟨9,_⟩ => (34942301 / 125000000 : ℝ)
  | ⟨10,_⟩ => (279932451 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (70081261 / 250000000 : ℝ)
  | ⟨12,_⟩ => (7017929 / 25000000 : ℝ)
  | ⟨13,_⟩ => (281107829 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281498431 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281887933 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (70569123 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282664119 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (35381351 / 125000000 : ℝ)
  | ⟨19,_⟩ => (283436567 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283821399 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56841063 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284588307 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284969887 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (57070211 / 200000000 : ℝ)
  | ⟨25,_⟩ => (142865431 / 500000000 : ℝ)
  | ⟨26,_⟩ => (35763783 / 125000000 : ℝ)
  | ⟨27,_⟩ => (286488267 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286865373 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287241583 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (719041 / 2500000 : ℝ)
  | ⟨31,_⟩ => (17999427 / 62500000 : ℝ)
  | ⟨32,_⟩ => (288364383 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (9023017 / 31250000 : ℝ)
  | ⟨34,_⟩ => (28910783 / 100000000 : ℝ)
  | ⟨35,_⟩ => (289478243 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (14492389 / 50000000 : ℝ)
  | ⟨37,_⟩ => (145108229 / 500000000 : ℝ)
  | ⟨38,_⟩ => (29058427 / 100000000 : ℝ)
  | ⟨39,_⟩ => (29095071 / 100000000 : ℝ)
  | ⟨40,_⟩ => (29131629 / 100000000 : ℝ)
  | ⟨41,_⟩ => (291681019 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (9126403 / 31250000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12282Cell0 :
    0 ≤ cap12282 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨0,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12282 ⟨0,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨0,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell1 :
    0 ≤ cap12282 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨1,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12282 ⟨1,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨1,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell2 :
    0 ≤ cap12282 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨2,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12282 ⟨2,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨2,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell3 :
    0 ≤ cap12282 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨3,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12282 ⟨3,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨3,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell4 :
    0 ≤ cap12282 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨4,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12282 ⟨4,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨4,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell5 :
    0 ≤ cap12282 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨5,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12282 ⟨5,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨5,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell6 :
    0 ≤ cap12282 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨6,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12282 ⟨6,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨6,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell7 :
    0 ≤ cap12282 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨7,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12282 ⟨7,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨7,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell8 :
    0 ≤ cap12282 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨8,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12282 ⟨8,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨8,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell9 :
    0 ≤ cap12282 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨9,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12282 ⟨9,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨9,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell10 :
    0 ≤ cap12282 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨10,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12282 ⟨10,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨10,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell11 :
    0 ≤ cap12282 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨11,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12282 ⟨11,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨11,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell12 :
    0 ≤ cap12282 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨12,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12282 ⟨12,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨12,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell13 :
    0 ≤ cap12282 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨13,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12282 ⟨13,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨13,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell14 :
    0 ≤ cap12282 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨14,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12282 ⟨14,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨14,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell15 :
    0 ≤ cap12282 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨15,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12282 ⟨15,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨15,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell16 :
    0 ≤ cap12282 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨16,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12282 ⟨16,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨16,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell17 :
    0 ≤ cap12282 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨17,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12282 ⟨17,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨17,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell18 :
    0 ≤ cap12282 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨18,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12282 ⟨18,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨18,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell19 :
    0 ≤ cap12282 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨19,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12282 ⟨19,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨19,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell20 :
    0 ≤ cap12282 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨20,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12282 ⟨20,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨20,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell21 :
    0 ≤ cap12282 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨21,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12282 ⟨21,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨21,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell22 :
    0 ≤ cap12282 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨22,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12282 ⟨22,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨22,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell23 :
    0 ≤ cap12282 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨23,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12282 ⟨23,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨23,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell24 :
    0 ≤ cap12282 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨24,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12282 ⟨24,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨24,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell25 :
    0 ≤ cap12282 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨25,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12282 ⟨25,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨25,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell26 :
    0 ≤ cap12282 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨26,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12282 ⟨26,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨26,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell27 :
    0 ≤ cap12282 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨27,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12282 ⟨27,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨27,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell28 :
    0 ≤ cap12282 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨28,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12282 ⟨28,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨28,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell29 :
    0 ≤ cap12282 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨29,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12282 ⟨29,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨29,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell30 :
    0 ≤ cap12282 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨30,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12282 ⟨30,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨30,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell31 :
    0 ≤ cap12282 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨31,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12282 ⟨31,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨31,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell32 :
    0 ≤ cap12282 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨32,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12282 ⟨32,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨32,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell33 :
    0 ≤ cap12282 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨33,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12282 ⟨33,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨33,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell34 :
    0 ≤ cap12282 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨34,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12282 ⟨34,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨34,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell35 :
    0 ≤ cap12282 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨35,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12282 ⟨35,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨35,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell36 :
    0 ≤ cap12282 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨36,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12282 ⟨36,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨36,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell37 :
    0 ≤ cap12282 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨37,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12282 ⟨37,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨37,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell38 :
    0 ≤ cap12282 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨38,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12282 ⟨38,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨38,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell39 :
    0 ≤ cap12282 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨39,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12282 ⟨39,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨39,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell40 :
    0 ≤ cap12282 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨40,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12282 ⟨40,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨40,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell41 :
    0 ≤ cap12282 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨41,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12282 ⟨41,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨41,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cell42 :
    0 ≤ cap12282 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12282 (parameters ⟨42,by decide⟩)
      (scalarRow12282.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12282 ⟨42,by decide⟩ ∧
    (scalarRow12282.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 ⟨42,by decide⟩ + (scalarRow12282.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12282.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12282.targetFrame := by
  norm_num [cap12282, scalarRow12282, sourceIndex, cell12282, BstLean.Part263.envelope, parameters]

theorem repair12282Cells (j : Fin 43) :
    0 ≤ cap12282 j ∧
    BstLean.Part263.envelope 12282 (parameters j) (scalarRow12282.table (sourceIndex j)).upper ≤ cap12282 j ∧
    (scalarRow12282.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12282 j + (scalarRow12282.table (sourceIndex j)).centre) /
      (scalarRow12282.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12282.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12282Cell0
  | ⟨1,_⟩ => exact repair12282Cell1
  | ⟨2,_⟩ => exact repair12282Cell2
  | ⟨3,_⟩ => exact repair12282Cell3
  | ⟨4,_⟩ => exact repair12282Cell4
  | ⟨5,_⟩ => exact repair12282Cell5
  | ⟨6,_⟩ => exact repair12282Cell6
  | ⟨7,_⟩ => exact repair12282Cell7
  | ⟨8,_⟩ => exact repair12282Cell8
  | ⟨9,_⟩ => exact repair12282Cell9
  | ⟨10,_⟩ => exact repair12282Cell10
  | ⟨11,_⟩ => exact repair12282Cell11
  | ⟨12,_⟩ => exact repair12282Cell12
  | ⟨13,_⟩ => exact repair12282Cell13
  | ⟨14,_⟩ => exact repair12282Cell14
  | ⟨15,_⟩ => exact repair12282Cell15
  | ⟨16,_⟩ => exact repair12282Cell16
  | ⟨17,_⟩ => exact repair12282Cell17
  | ⟨18,_⟩ => exact repair12282Cell18
  | ⟨19,_⟩ => exact repair12282Cell19
  | ⟨20,_⟩ => exact repair12282Cell20
  | ⟨21,_⟩ => exact repair12282Cell21
  | ⟨22,_⟩ => exact repair12282Cell22
  | ⟨23,_⟩ => exact repair12282Cell23
  | ⟨24,_⟩ => exact repair12282Cell24
  | ⟨25,_⟩ => exact repair12282Cell25
  | ⟨26,_⟩ => exact repair12282Cell26
  | ⟨27,_⟩ => exact repair12282Cell27
  | ⟨28,_⟩ => exact repair12282Cell28
  | ⟨29,_⟩ => exact repair12282Cell29
  | ⟨30,_⟩ => exact repair12282Cell30
  | ⟨31,_⟩ => exact repair12282Cell31
  | ⟨32,_⟩ => exact repair12282Cell32
  | ⟨33,_⟩ => exact repair12282Cell33
  | ⟨34,_⟩ => exact repair12282Cell34
  | ⟨35,_⟩ => exact repair12282Cell35
  | ⟨36,_⟩ => exact repair12282Cell36
  | ⟨37,_⟩ => exact repair12282Cell37
  | ⟨38,_⟩ => exact repair12282Cell38
  | ⟨39,_⟩ => exact repair12282Cell39
  | ⟨40,_⟩ => exact repair12282Cell40
  | ⟨41,_⟩ => exact repair12282Cell41
  | ⟨42,_⟩ => exact repair12282Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12282 : FrameRepair 12282 scalarRow12282 where
  cap := cap12282
  cap_nonneg := fun j => (repair12282Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12282])
  endpoint := fun j => (repair12282Cells j).2.1
  endpoint_upper := fun j => (repair12282Cells j).2.2.1
  frame := fun j => (repair12282Cells j).2.2.2

noncomputable def cap12283 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275948339 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138175617 / 500000000 : ℝ)
  | ⟨2,_⟩ => (55350627 / 200000000 : ℝ)
  | ⟨3,_⟩ => (277154037 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (5551079 / 20000000 : ℝ)
  | ⟨5,_⟩ => (34744109 / 125000000 : ℝ)
  | ⟨6,_⟩ => (139175167 / 500000000 : ℝ)
  | ⟨7,_⟩ => (278747289 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (69785817 / 250000000 : ℝ)
  | ⟨9,_⟩ => (11181531 / 40000000 : ℝ)
  | ⟨10,_⟩ => (279932311 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140162449 / 500000000 : ℝ)
  | ⟨12,_⟩ => (17544813 / 62500000 : ℝ)
  | ⟨13,_⟩ => (281107671 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140749133 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140943881 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141138157 / 500000000 : ℝ)
  | ⟨17,_⟩ => (552078 / 1953125 : ℝ)
  | ⟨18,_⟩ => (141525309 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283436371 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283821197 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (142102553 / 500000000 : ℝ)
  | ⟨22,_⟩ => (71147023 / 250000000 : ℝ)
  | ⟨23,_⟩ => (142484833 / 500000000 : ℝ)
  | ⟨24,_⟩ => (71337707 / 250000000 : ℝ)
  | ⟨25,_⟩ => (285730629 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (11444401 / 40000000 : ℝ)
  | ⟨27,_⟩ => (286488021 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286865121 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (11489653 / 40000000 : ℝ)
  | ⟨30,_⟩ => (35952017 / 125000000 : ℝ)
  | ⟨31,_⟩ => (143995281 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288364107 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144368131 / 500000000 : ℝ)
  | ⟨34,_⟩ => (289107541 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289477949 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (7246187 / 25000000 : ℝ)
  | ⟨37,_⟩ => (290216151 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145291979 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290950391 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145657983 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291680689 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (3650557 / 12500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12283Cell0 :
    0 ≤ cap12283 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨0,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12283 ⟨0,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨0,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell1 :
    0 ≤ cap12283 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨1,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12283 ⟨1,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨1,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell2 :
    0 ≤ cap12283 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨2,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12283 ⟨2,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨2,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell3 :
    0 ≤ cap12283 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨3,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12283 ⟨3,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨3,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell4 :
    0 ≤ cap12283 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨4,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12283 ⟨4,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨4,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell5 :
    0 ≤ cap12283 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨5,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12283 ⟨5,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨5,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell6 :
    0 ≤ cap12283 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨6,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12283 ⟨6,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨6,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell7 :
    0 ≤ cap12283 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨7,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12283 ⟨7,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨7,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell8 :
    0 ≤ cap12283 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨8,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12283 ⟨8,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨8,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell9 :
    0 ≤ cap12283 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨9,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12283 ⟨9,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨9,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell10 :
    0 ≤ cap12283 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨10,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12283 ⟨10,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨10,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell11 :
    0 ≤ cap12283 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨11,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12283 ⟨11,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨11,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell12 :
    0 ≤ cap12283 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨12,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12283 ⟨12,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨12,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell13 :
    0 ≤ cap12283 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨13,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12283 ⟨13,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨13,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell14 :
    0 ≤ cap12283 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨14,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12283 ⟨14,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨14,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell15 :
    0 ≤ cap12283 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨15,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12283 ⟨15,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨15,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell16 :
    0 ≤ cap12283 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨16,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12283 ⟨16,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨16,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell17 :
    0 ≤ cap12283 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨17,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12283 ⟨17,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨17,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell18 :
    0 ≤ cap12283 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨18,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12283 ⟨18,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨18,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell19 :
    0 ≤ cap12283 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨19,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12283 ⟨19,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨19,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell20 :
    0 ≤ cap12283 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨20,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12283 ⟨20,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨20,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell21 :
    0 ≤ cap12283 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨21,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12283 ⟨21,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨21,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell22 :
    0 ≤ cap12283 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨22,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12283 ⟨22,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨22,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell23 :
    0 ≤ cap12283 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨23,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12283 ⟨23,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨23,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell24 :
    0 ≤ cap12283 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨24,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12283 ⟨24,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨24,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell25 :
    0 ≤ cap12283 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨25,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12283 ⟨25,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨25,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell26 :
    0 ≤ cap12283 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨26,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12283 ⟨26,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨26,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell27 :
    0 ≤ cap12283 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨27,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12283 ⟨27,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨27,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell28 :
    0 ≤ cap12283 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨28,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12283 ⟨28,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨28,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell29 :
    0 ≤ cap12283 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨29,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12283 ⟨29,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨29,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell30 :
    0 ≤ cap12283 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨30,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12283 ⟨30,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨30,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell31 :
    0 ≤ cap12283 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨31,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12283 ⟨31,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨31,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell32 :
    0 ≤ cap12283 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨32,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12283 ⟨32,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨32,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell33 :
    0 ≤ cap12283 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨33,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12283 ⟨33,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨33,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell34 :
    0 ≤ cap12283 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨34,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12283 ⟨34,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨34,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell35 :
    0 ≤ cap12283 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨35,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12283 ⟨35,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨35,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell36 :
    0 ≤ cap12283 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨36,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12283 ⟨36,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨36,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell37 :
    0 ≤ cap12283 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨37,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12283 ⟨37,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨37,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell38 :
    0 ≤ cap12283 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨38,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12283 ⟨38,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨38,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell39 :
    0 ≤ cap12283 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨39,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12283 ⟨39,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨39,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell40 :
    0 ≤ cap12283 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨40,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12283 ⟨40,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨40,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell41 :
    0 ≤ cap12283 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨41,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12283 ⟨41,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨41,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cell42 :
    0 ≤ cap12283 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12283 (parameters ⟨42,by decide⟩)
      (scalarRow12283.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12283 ⟨42,by decide⟩ ∧
    (scalarRow12283.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 ⟨42,by decide⟩ + (scalarRow12283.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12283.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12283.targetFrame := by
  norm_num [cap12283, scalarRow12283, sourceIndex, cell12283, BstLean.Part263.envelope, parameters]

theorem repair12283Cells (j : Fin 43) :
    0 ≤ cap12283 j ∧
    BstLean.Part263.envelope 12283 (parameters j) (scalarRow12283.table (sourceIndex j)).upper ≤ cap12283 j ∧
    (scalarRow12283.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12283 j + (scalarRow12283.table (sourceIndex j)).centre) /
      (scalarRow12283.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12283.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12283Cell0
  | ⟨1,_⟩ => exact repair12283Cell1
  | ⟨2,_⟩ => exact repair12283Cell2
  | ⟨3,_⟩ => exact repair12283Cell3
  | ⟨4,_⟩ => exact repair12283Cell4
  | ⟨5,_⟩ => exact repair12283Cell5
  | ⟨6,_⟩ => exact repair12283Cell6
  | ⟨7,_⟩ => exact repair12283Cell7
  | ⟨8,_⟩ => exact repair12283Cell8
  | ⟨9,_⟩ => exact repair12283Cell9
  | ⟨10,_⟩ => exact repair12283Cell10
  | ⟨11,_⟩ => exact repair12283Cell11
  | ⟨12,_⟩ => exact repair12283Cell12
  | ⟨13,_⟩ => exact repair12283Cell13
  | ⟨14,_⟩ => exact repair12283Cell14
  | ⟨15,_⟩ => exact repair12283Cell15
  | ⟨16,_⟩ => exact repair12283Cell16
  | ⟨17,_⟩ => exact repair12283Cell17
  | ⟨18,_⟩ => exact repair12283Cell18
  | ⟨19,_⟩ => exact repair12283Cell19
  | ⟨20,_⟩ => exact repair12283Cell20
  | ⟨21,_⟩ => exact repair12283Cell21
  | ⟨22,_⟩ => exact repair12283Cell22
  | ⟨23,_⟩ => exact repair12283Cell23
  | ⟨24,_⟩ => exact repair12283Cell24
  | ⟨25,_⟩ => exact repair12283Cell25
  | ⟨26,_⟩ => exact repair12283Cell26
  | ⟨27,_⟩ => exact repair12283Cell27
  | ⟨28,_⟩ => exact repair12283Cell28
  | ⟨29,_⟩ => exact repair12283Cell29
  | ⟨30,_⟩ => exact repair12283Cell30
  | ⟨31,_⟩ => exact repair12283Cell31
  | ⟨32,_⟩ => exact repair12283Cell32
  | ⟨33,_⟩ => exact repair12283Cell33
  | ⟨34,_⟩ => exact repair12283Cell34
  | ⟨35,_⟩ => exact repair12283Cell35
  | ⟨36,_⟩ => exact repair12283Cell36
  | ⟨37,_⟩ => exact repair12283Cell37
  | ⟨38,_⟩ => exact repair12283Cell38
  | ⟨39,_⟩ => exact repair12283Cell39
  | ⟨40,_⟩ => exact repair12283Cell40
  | ⟨41,_⟩ => exact repair12283Cell41
  | ⟨42,_⟩ => exact repair12283Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12283 : FrameRepair 12283 scalarRow12283 where
  cap := cap12283
  cap_nonneg := fun j => (repair12283Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12283])
  endpoint := fun j => (repair12283Cells j).2.1
  endpoint_upper := fun j => (repair12283Cells j).2.2.1
  frame := fun j => (repair12283Cells j).2.2.2

noncomputable def cap12284 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34493533 / 125000000 : ℝ)
  | ⟨1,_⟩ => (17271947 / 62500000 : ℝ)
  | ⟨2,_⟩ => (138376523 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138576971 / 500000000 : ℝ)
  | ⟨4,_⟩ => (34694231 / 125000000 : ℝ)
  | ⟨5,_⟩ => (69488191 / 250000000 : ℝ)
  | ⟨6,_⟩ => (278350219 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (8710849 / 31250000 : ℝ)
  | ⟨8,_⟩ => (279143141 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139769071 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279932171 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (17520297 / 62500000 : ℝ)
  | ⟨12,_⟩ => (35089607 / 125000000 : ℝ)
  | ⟨13,_⟩ => (35138439 / 125000000 : ℝ)
  | ⟨14,_⟩ => (281498101 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (28188759 / 100000000 : ℝ)
  | ⟨16,_⟩ => (282276137 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (35332969 / 125000000 : ℝ)
  | ⟨18,_⟩ => (283050427 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (11337447 / 40000000 : ℝ)
  | ⟨20,_⟩ => (141910497 / 500000000 : ℝ)
  | ⟨21,_⟩ => (142102449 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284587877 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (56993889 / 200000000 : ℝ)
  | ⟨24,_⟩ => (285350601 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (57146079 / 200000000 : ℝ)
  | ⟨26,_⟩ => (57221957 / 200000000 : ℝ)
  | ⟨27,_⟩ => (8952743 / 31250000 : ℝ)
  | ⟨28,_⟩ => (286864869 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287241067 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (2246999 / 7812500 : ℝ)
  | ⟨31,_⟩ => (71997573 / 250000000 : ℝ)
  | ⟨32,_⟩ => (288363831 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288735979 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289107253 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (57895531 / 200000000 : ℝ)
  | ⟨36,_⟩ => (289847179 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (58043169 / 200000000 : ℝ)
  | ⟨38,_⟩ => (58116729 / 200000000 : ℝ)
  | ⟨39,_⟩ => (290950073 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145657821 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291680359 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (4563191 / 15625000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12284Cell0 :
    0 ≤ cap12284 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨0,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12284 ⟨0,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨0,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell1 :
    0 ≤ cap12284 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨1,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12284 ⟨1,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨1,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell2 :
    0 ≤ cap12284 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨2,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12284 ⟨2,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨2,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell3 :
    0 ≤ cap12284 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨3,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12284 ⟨3,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨3,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell4 :
    0 ≤ cap12284 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨4,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12284 ⟨4,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨4,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell5 :
    0 ≤ cap12284 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨5,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12284 ⟨5,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨5,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell6 :
    0 ≤ cap12284 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨6,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12284 ⟨6,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨6,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell7 :
    0 ≤ cap12284 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨7,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12284 ⟨7,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨7,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell8 :
    0 ≤ cap12284 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨8,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12284 ⟨8,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨8,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell9 :
    0 ≤ cap12284 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨9,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12284 ⟨9,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨9,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell10 :
    0 ≤ cap12284 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨10,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12284 ⟨10,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨10,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell11 :
    0 ≤ cap12284 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨11,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12284 ⟨11,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨11,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell12 :
    0 ≤ cap12284 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨12,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12284 ⟨12,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨12,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell13 :
    0 ≤ cap12284 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨13,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12284 ⟨13,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨13,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell14 :
    0 ≤ cap12284 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨14,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12284 ⟨14,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨14,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell15 :
    0 ≤ cap12284 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨15,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12284 ⟨15,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨15,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell16 :
    0 ≤ cap12284 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨16,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12284 ⟨16,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨16,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell17 :
    0 ≤ cap12284 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨17,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12284 ⟨17,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨17,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell18 :
    0 ≤ cap12284 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨18,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12284 ⟨18,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨18,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell19 :
    0 ≤ cap12284 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨19,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12284 ⟨19,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨19,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell20 :
    0 ≤ cap12284 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨20,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12284 ⟨20,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨20,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell21 :
    0 ≤ cap12284 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨21,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12284 ⟨21,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨21,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell22 :
    0 ≤ cap12284 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨22,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12284 ⟨22,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨22,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell23 :
    0 ≤ cap12284 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨23,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12284 ⟨23,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨23,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell24 :
    0 ≤ cap12284 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨24,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12284 ⟨24,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨24,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell25 :
    0 ≤ cap12284 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨25,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12284 ⟨25,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨25,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell26 :
    0 ≤ cap12284 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨26,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12284 ⟨26,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨26,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell27 :
    0 ≤ cap12284 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨27,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12284 ⟨27,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨27,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell28 :
    0 ≤ cap12284 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨28,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12284 ⟨28,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨28,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell29 :
    0 ≤ cap12284 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨29,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12284 ⟨29,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨29,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell30 :
    0 ≤ cap12284 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨30,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12284 ⟨30,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨30,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell31 :
    0 ≤ cap12284 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨31,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12284 ⟨31,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨31,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell32 :
    0 ≤ cap12284 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨32,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12284 ⟨32,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨32,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell33 :
    0 ≤ cap12284 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨33,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12284 ⟨33,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨33,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell34 :
    0 ≤ cap12284 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨34,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12284 ⟨34,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨34,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell35 :
    0 ≤ cap12284 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨35,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12284 ⟨35,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨35,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell36 :
    0 ≤ cap12284 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨36,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12284 ⟨36,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨36,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell37 :
    0 ≤ cap12284 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨37,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12284 ⟨37,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨37,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell38 :
    0 ≤ cap12284 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨38,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12284 ⟨38,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨38,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell39 :
    0 ≤ cap12284 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨39,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12284 ⟨39,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨39,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell40 :
    0 ≤ cap12284 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨40,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12284 ⟨40,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨40,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell41 :
    0 ≤ cap12284 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨41,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12284 ⟨41,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨41,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cell42 :
    0 ≤ cap12284 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12284 (parameters ⟨42,by decide⟩)
      (scalarRow12284.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12284 ⟨42,by decide⟩ ∧
    (scalarRow12284.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 ⟨42,by decide⟩ + (scalarRow12284.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12284.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12284.targetFrame := by
  norm_num [cap12284, scalarRow12284, sourceIndex, cell12284, BstLean.Part263.envelope, parameters]

theorem repair12284Cells (j : Fin 43) :
    0 ≤ cap12284 j ∧
    BstLean.Part263.envelope 12284 (parameters j) (scalarRow12284.table (sourceIndex j)).upper ≤ cap12284 j ∧
    (scalarRow12284.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12284 j + (scalarRow12284.table (sourceIndex j)).centre) /
      (scalarRow12284.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12284.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12284Cell0
  | ⟨1,_⟩ => exact repair12284Cell1
  | ⟨2,_⟩ => exact repair12284Cell2
  | ⟨3,_⟩ => exact repair12284Cell3
  | ⟨4,_⟩ => exact repair12284Cell4
  | ⟨5,_⟩ => exact repair12284Cell5
  | ⟨6,_⟩ => exact repair12284Cell6
  | ⟨7,_⟩ => exact repair12284Cell7
  | ⟨8,_⟩ => exact repair12284Cell8
  | ⟨9,_⟩ => exact repair12284Cell9
  | ⟨10,_⟩ => exact repair12284Cell10
  | ⟨11,_⟩ => exact repair12284Cell11
  | ⟨12,_⟩ => exact repair12284Cell12
  | ⟨13,_⟩ => exact repair12284Cell13
  | ⟨14,_⟩ => exact repair12284Cell14
  | ⟨15,_⟩ => exact repair12284Cell15
  | ⟨16,_⟩ => exact repair12284Cell16
  | ⟨17,_⟩ => exact repair12284Cell17
  | ⟨18,_⟩ => exact repair12284Cell18
  | ⟨19,_⟩ => exact repair12284Cell19
  | ⟨20,_⟩ => exact repair12284Cell20
  | ⟨21,_⟩ => exact repair12284Cell21
  | ⟨22,_⟩ => exact repair12284Cell22
  | ⟨23,_⟩ => exact repair12284Cell23
  | ⟨24,_⟩ => exact repair12284Cell24
  | ⟨25,_⟩ => exact repair12284Cell25
  | ⟨26,_⟩ => exact repair12284Cell26
  | ⟨27,_⟩ => exact repair12284Cell27
  | ⟨28,_⟩ => exact repair12284Cell28
  | ⟨29,_⟩ => exact repair12284Cell29
  | ⟨30,_⟩ => exact repair12284Cell30
  | ⟨31,_⟩ => exact repair12284Cell31
  | ⟨32,_⟩ => exact repair12284Cell32
  | ⟨33,_⟩ => exact repair12284Cell33
  | ⟨34,_⟩ => exact repair12284Cell34
  | ⟨35,_⟩ => exact repair12284Cell35
  | ⟨36,_⟩ => exact repair12284Cell36
  | ⟨37,_⟩ => exact repair12284Cell37
  | ⟨38,_⟩ => exact repair12284Cell38
  | ⟨39,_⟩ => exact repair12284Cell39
  | ⟨40,_⟩ => exact repair12284Cell40
  | ⟨41,_⟩ => exact repair12284Cell41
  | ⟨42,_⟩ => exact repair12284Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12284 : FrameRepair 12284 scalarRow12284 where
  cap := cap12284
  cap_nonneg := fun j => (repair12284Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12284])
  endpoint := fun j => (repair12284Cells j).2.1
  endpoint_upper := fun j => (repair12284Cells j).2.2.1
  frame := fun j => (repair12284Cells j).2.2.2

noncomputable def cap12285 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68987047 / 250000000 : ℝ)
  | ⟨1,_⟩ => (27635107 / 100000000 : ℝ)
  | ⟨2,_⟩ => (138376479 / 500000000 : ℝ)
  | ⟨3,_⟩ => (34644231 / 125000000 : ℝ)
  | ⟨4,_⟩ => (277553747 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277952657 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55670021 / 200000000 : ℝ)
  | ⟨7,_⟩ => (34843381 / 125000000 : ℝ)
  | ⟨8,_⟩ => (139571507 / 500000000 : ℝ)
  | ⟨9,_⟩ => (34942251 / 125000000 : ℝ)
  | ⟨10,_⟩ => (2186969 / 7812500 : ℝ)
  | ⟨11,_⟩ => (140162303 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280716703 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281107353 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (17593621 / 62500000 : ℝ)
  | ⟨15,_⟩ => (281887419 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282275959 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (17666473 / 62500000 : ℝ)
  | ⟨18,_⟩ => (283050237 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141717989 / 500000000 : ℝ)
  | ⟨20,_⟩ => (35477599 / 125000000 : ℝ)
  | ⟨21,_⟩ => (284204689 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142293831 / 500000000 : ℝ)
  | ⟨23,_⟩ => (35621153 / 125000000 : ℝ)
  | ⟨24,_⟩ => (142675187 / 500000000 : ℝ)
  | ⟨25,_⟩ => (142865081 / 500000000 : ℝ)
  | ⟨26,_⟩ => (143054773 / 500000000 : ℝ)
  | ⟨27,_⟩ => (28648753 / 100000000 : ℝ)
  | ⟨28,_⟩ => (143432309 / 500000000 : ℝ)
  | ⟨29,_⟩ => (28724081 / 100000000 : ℝ)
  | ⟨30,_⟩ => (35951951 / 125000000 : ℝ)
  | ⟨31,_⟩ => (143995011 / 500000000 : ℝ)
  | ⟨32,_⟩ => (57672711 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288735697 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (57821393 / 200000000 : ℝ)
  | ⟨35,_⟩ => (3618467 / 12500000 : ℝ)
  | ⟨36,_⟩ => (289846879 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290215539 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290583333 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (58189951 / 200000000 : ℝ)
  | ⟨40,_⟩ => (291315317 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (72920007 / 250000000 : ℝ)
  | ⟨42,_⟩ => (18252743 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12285Cell0 :
    0 ≤ cap12285 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨0,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12285 ⟨0,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨0,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell1 :
    0 ≤ cap12285 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨1,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12285 ⟨1,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨1,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell2 :
    0 ≤ cap12285 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨2,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12285 ⟨2,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨2,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell3 :
    0 ≤ cap12285 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨3,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12285 ⟨3,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨3,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell4 :
    0 ≤ cap12285 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨4,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12285 ⟨4,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨4,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell5 :
    0 ≤ cap12285 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨5,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12285 ⟨5,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨5,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell6 :
    0 ≤ cap12285 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨6,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12285 ⟨6,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨6,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell7 :
    0 ≤ cap12285 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨7,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12285 ⟨7,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨7,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell8 :
    0 ≤ cap12285 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨8,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12285 ⟨8,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨8,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell9 :
    0 ≤ cap12285 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨9,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12285 ⟨9,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨9,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell10 :
    0 ≤ cap12285 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨10,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12285 ⟨10,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨10,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell11 :
    0 ≤ cap12285 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨11,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12285 ⟨11,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨11,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell12 :
    0 ≤ cap12285 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨12,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12285 ⟨12,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨12,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell13 :
    0 ≤ cap12285 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨13,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12285 ⟨13,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨13,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell14 :
    0 ≤ cap12285 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨14,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12285 ⟨14,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨14,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell15 :
    0 ≤ cap12285 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨15,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12285 ⟨15,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨15,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell16 :
    0 ≤ cap12285 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨16,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12285 ⟨16,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨16,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell17 :
    0 ≤ cap12285 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨17,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12285 ⟨17,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨17,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell18 :
    0 ≤ cap12285 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨18,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12285 ⟨18,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨18,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell19 :
    0 ≤ cap12285 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨19,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12285 ⟨19,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨19,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell20 :
    0 ≤ cap12285 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨20,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12285 ⟨20,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨20,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell21 :
    0 ≤ cap12285 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨21,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12285 ⟨21,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨21,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell22 :
    0 ≤ cap12285 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨22,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12285 ⟨22,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨22,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell23 :
    0 ≤ cap12285 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨23,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12285 ⟨23,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨23,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell24 :
    0 ≤ cap12285 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨24,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12285 ⟨24,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨24,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell25 :
    0 ≤ cap12285 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨25,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12285 ⟨25,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨25,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell26 :
    0 ≤ cap12285 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨26,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12285 ⟨26,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨26,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell27 :
    0 ≤ cap12285 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨27,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12285 ⟨27,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨27,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell28 :
    0 ≤ cap12285 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨28,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12285 ⟨28,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨28,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell29 :
    0 ≤ cap12285 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨29,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12285 ⟨29,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨29,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell30 :
    0 ≤ cap12285 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨30,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12285 ⟨30,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨30,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell31 :
    0 ≤ cap12285 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨31,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12285 ⟨31,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨31,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell32 :
    0 ≤ cap12285 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨32,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12285 ⟨32,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨32,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell33 :
    0 ≤ cap12285 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨33,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12285 ⟨33,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨33,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell34 :
    0 ≤ cap12285 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨34,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12285 ⟨34,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨34,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell35 :
    0 ≤ cap12285 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨35,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12285 ⟨35,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨35,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell36 :
    0 ≤ cap12285 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨36,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12285 ⟨36,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨36,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell37 :
    0 ≤ cap12285 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨37,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12285 ⟨37,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨37,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell38 :
    0 ≤ cap12285 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨38,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12285 ⟨38,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨38,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell39 :
    0 ≤ cap12285 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨39,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12285 ⟨39,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨39,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell40 :
    0 ≤ cap12285 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨40,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12285 ⟨40,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨40,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell41 :
    0 ≤ cap12285 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨41,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12285 ⟨41,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨41,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cell42 :
    0 ≤ cap12285 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12285 (parameters ⟨42,by decide⟩)
      (scalarRow12285.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12285 ⟨42,by decide⟩ ∧
    (scalarRow12285.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 ⟨42,by decide⟩ + (scalarRow12285.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12285.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12285.targetFrame := by
  norm_num [cap12285, scalarRow12285, sourceIndex, cell12285, BstLean.Part263.envelope, parameters]

theorem repair12285Cells (j : Fin 43) :
    0 ≤ cap12285 j ∧
    BstLean.Part263.envelope 12285 (parameters j) (scalarRow12285.table (sourceIndex j)).upper ≤ cap12285 j ∧
    (scalarRow12285.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12285 j + (scalarRow12285.table (sourceIndex j)).centre) /
      (scalarRow12285.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12285.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12285Cell0
  | ⟨1,_⟩ => exact repair12285Cell1
  | ⟨2,_⟩ => exact repair12285Cell2
  | ⟨3,_⟩ => exact repair12285Cell3
  | ⟨4,_⟩ => exact repair12285Cell4
  | ⟨5,_⟩ => exact repair12285Cell5
  | ⟨6,_⟩ => exact repair12285Cell6
  | ⟨7,_⟩ => exact repair12285Cell7
  | ⟨8,_⟩ => exact repair12285Cell8
  | ⟨9,_⟩ => exact repair12285Cell9
  | ⟨10,_⟩ => exact repair12285Cell10
  | ⟨11,_⟩ => exact repair12285Cell11
  | ⟨12,_⟩ => exact repair12285Cell12
  | ⟨13,_⟩ => exact repair12285Cell13
  | ⟨14,_⟩ => exact repair12285Cell14
  | ⟨15,_⟩ => exact repair12285Cell15
  | ⟨16,_⟩ => exact repair12285Cell16
  | ⟨17,_⟩ => exact repair12285Cell17
  | ⟨18,_⟩ => exact repair12285Cell18
  | ⟨19,_⟩ => exact repair12285Cell19
  | ⟨20,_⟩ => exact repair12285Cell20
  | ⟨21,_⟩ => exact repair12285Cell21
  | ⟨22,_⟩ => exact repair12285Cell22
  | ⟨23,_⟩ => exact repair12285Cell23
  | ⟨24,_⟩ => exact repair12285Cell24
  | ⟨25,_⟩ => exact repair12285Cell25
  | ⟨26,_⟩ => exact repair12285Cell26
  | ⟨27,_⟩ => exact repair12285Cell27
  | ⟨28,_⟩ => exact repair12285Cell28
  | ⟨29,_⟩ => exact repair12285Cell29
  | ⟨30,_⟩ => exact repair12285Cell30
  | ⟨31,_⟩ => exact repair12285Cell31
  | ⟨32,_⟩ => exact repair12285Cell32
  | ⟨33,_⟩ => exact repair12285Cell33
  | ⟨34,_⟩ => exact repair12285Cell34
  | ⟨35,_⟩ => exact repair12285Cell35
  | ⟨36,_⟩ => exact repair12285Cell36
  | ⟨37,_⟩ => exact repair12285Cell37
  | ⟨38,_⟩ => exact repair12285Cell38
  | ⟨39,_⟩ => exact repair12285Cell39
  | ⟨40,_⟩ => exact repair12285Cell40
  | ⟨41,_⟩ => exact repair12285Cell41
  | ⟨42,_⟩ => exact repair12285Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12285 : FrameRepair 12285 scalarRow12285 where
  cap := cap12285
  cap_nonneg := fun j => (repair12285Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12285])
  endpoint := fun j => (repair12285Cells j).2.1
  endpoint_upper := fun j => (repair12285Cells j).2.2.1
  frame := fun j => (repair12285Cells j).2.2.2

noncomputable def cap12286 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275948113 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (69087747 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276752869 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277153753 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138776823 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277952549 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278349991 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278746927 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279142887 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (2236303 / 8000000 : ℝ)
  | ⟨10,_⟩ => (69982973 / 250000000 : ℝ)
  | ⟨11,_⟩ => (14016223 / 50000000 : ℝ)
  | ⟨12,_⟩ => (280716551 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (56221439 / 200000000 : ℝ)
  | ⟨14,_⟩ => (281497771 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (17617953 / 62500000 : ℝ)
  | ⟨16,_⟩ => (141137891 / 500000000 : ℝ)
  | ⟨17,_⟩ => (35332923 / 125000000 : ℝ)
  | ⟨18,_⟩ => (283050047 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141717891 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283820589 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (888139 / 3125000 : ℝ)
  | ⟨22,_⟩ => (284587447 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284969003 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142675073 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285729929 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143054653 / 500000000 : ℝ)
  | ⟨27,_⟩ => (71621821 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143432183 / 500000000 : ℝ)
  | ⟨29,_⟩ => (35905069 / 125000000 : ℝ)
  | ⟨30,_⟩ => (17975959 / 62500000 : ℝ)
  | ⟨31,_⟩ => (35998719 / 125000000 : ℝ)
  | ⟨32,_⟩ => (144181639 / 500000000 : ℝ)
  | ⟨33,_⟩ => (57747083 / 200000000 : ℝ)
  | ⟨34,_⟩ => (72276669 / 250000000 : ℝ)
  | ⟨35,_⟩ => (144738533 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289846579 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (4534613 / 15625000 : ℝ)
  | ⟨38,_⟩ => (290583021 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (72737359 / 250000000 : ℝ)
  | ⟨40,_⟩ => (291314993 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145839849 / 500000000 : ℝ)
  | ⟨42,_⟩ => (9126361 / 31250000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12286Cell0 :
    0 ≤ cap12286 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨0,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12286 ⟨0,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨0,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell1 :
    0 ≤ cap12286 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨1,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12286 ⟨1,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨1,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell2 :
    0 ≤ cap12286 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨2,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12286 ⟨2,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨2,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell3 :
    0 ≤ cap12286 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨3,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12286 ⟨3,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨3,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell4 :
    0 ≤ cap12286 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨4,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12286 ⟨4,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨4,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell5 :
    0 ≤ cap12286 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨5,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12286 ⟨5,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨5,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell6 :
    0 ≤ cap12286 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨6,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12286 ⟨6,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨6,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell7 :
    0 ≤ cap12286 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨7,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12286 ⟨7,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨7,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell8 :
    0 ≤ cap12286 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨8,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12286 ⟨8,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨8,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell9 :
    0 ≤ cap12286 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨9,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12286 ⟨9,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨9,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell10 :
    0 ≤ cap12286 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨10,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12286 ⟨10,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨10,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell11 :
    0 ≤ cap12286 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨11,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12286 ⟨11,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨11,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell12 :
    0 ≤ cap12286 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨12,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12286 ⟨12,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨12,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell13 :
    0 ≤ cap12286 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨13,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12286 ⟨13,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨13,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell14 :
    0 ≤ cap12286 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨14,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12286 ⟨14,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨14,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell15 :
    0 ≤ cap12286 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨15,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12286 ⟨15,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨15,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell16 :
    0 ≤ cap12286 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨16,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12286 ⟨16,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨16,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell17 :
    0 ≤ cap12286 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨17,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12286 ⟨17,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨17,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell18 :
    0 ≤ cap12286 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨18,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12286 ⟨18,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨18,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell19 :
    0 ≤ cap12286 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨19,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12286 ⟨19,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨19,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell20 :
    0 ≤ cap12286 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨20,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12286 ⟨20,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨20,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell21 :
    0 ≤ cap12286 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨21,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12286 ⟨21,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨21,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell22 :
    0 ≤ cap12286 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨22,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12286 ⟨22,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨22,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell23 :
    0 ≤ cap12286 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨23,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12286 ⟨23,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨23,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell24 :
    0 ≤ cap12286 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨24,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12286 ⟨24,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨24,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell25 :
    0 ≤ cap12286 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨25,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12286 ⟨25,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨25,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell26 :
    0 ≤ cap12286 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨26,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12286 ⟨26,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨26,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell27 :
    0 ≤ cap12286 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨27,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12286 ⟨27,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨27,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell28 :
    0 ≤ cap12286 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨28,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12286 ⟨28,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨28,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell29 :
    0 ≤ cap12286 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨29,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12286 ⟨29,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨29,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell30 :
    0 ≤ cap12286 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨30,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12286 ⟨30,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨30,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell31 :
    0 ≤ cap12286 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨31,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12286 ⟨31,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨31,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell32 :
    0 ≤ cap12286 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨32,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12286 ⟨32,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨32,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell33 :
    0 ≤ cap12286 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨33,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12286 ⟨33,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨33,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell34 :
    0 ≤ cap12286 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨34,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12286 ⟨34,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨34,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell35 :
    0 ≤ cap12286 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨35,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12286 ⟨35,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨35,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell36 :
    0 ≤ cap12286 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨36,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12286 ⟨36,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨36,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell37 :
    0 ≤ cap12286 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨37,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12286 ⟨37,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨37,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell38 :
    0 ≤ cap12286 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨38,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12286 ⟨38,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨38,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell39 :
    0 ≤ cap12286 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨39,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12286 ⟨39,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨39,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell40 :
    0 ≤ cap12286 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨40,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12286 ⟨40,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨40,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell41 :
    0 ≤ cap12286 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨41,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12286 ⟨41,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨41,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cell42 :
    0 ≤ cap12286 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12286 (parameters ⟨42,by decide⟩)
      (scalarRow12286.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12286 ⟨42,by decide⟩ ∧
    (scalarRow12286.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 ⟨42,by decide⟩ + (scalarRow12286.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12286.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12286.targetFrame := by
  norm_num [cap12286, scalarRow12286, sourceIndex, cell12286, BstLean.Part263.envelope, parameters]

theorem repair12286Cells (j : Fin 43) :
    0 ≤ cap12286 j ∧
    BstLean.Part263.envelope 12286 (parameters j) (scalarRow12286.table (sourceIndex j)).upper ≤ cap12286 j ∧
    (scalarRow12286.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12286 j + (scalarRow12286.table (sourceIndex j)).centre) /
      (scalarRow12286.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12286.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12286Cell0
  | ⟨1,_⟩ => exact repair12286Cell1
  | ⟨2,_⟩ => exact repair12286Cell2
  | ⟨3,_⟩ => exact repair12286Cell3
  | ⟨4,_⟩ => exact repair12286Cell4
  | ⟨5,_⟩ => exact repair12286Cell5
  | ⟨6,_⟩ => exact repair12286Cell6
  | ⟨7,_⟩ => exact repair12286Cell7
  | ⟨8,_⟩ => exact repair12286Cell8
  | ⟨9,_⟩ => exact repair12286Cell9
  | ⟨10,_⟩ => exact repair12286Cell10
  | ⟨11,_⟩ => exact repair12286Cell11
  | ⟨12,_⟩ => exact repair12286Cell12
  | ⟨13,_⟩ => exact repair12286Cell13
  | ⟨14,_⟩ => exact repair12286Cell14
  | ⟨15,_⟩ => exact repair12286Cell15
  | ⟨16,_⟩ => exact repair12286Cell16
  | ⟨17,_⟩ => exact repair12286Cell17
  | ⟨18,_⟩ => exact repair12286Cell18
  | ⟨19,_⟩ => exact repair12286Cell19
  | ⟨20,_⟩ => exact repair12286Cell20
  | ⟨21,_⟩ => exact repair12286Cell21
  | ⟨22,_⟩ => exact repair12286Cell22
  | ⟨23,_⟩ => exact repair12286Cell23
  | ⟨24,_⟩ => exact repair12286Cell24
  | ⟨25,_⟩ => exact repair12286Cell25
  | ⟨26,_⟩ => exact repair12286Cell26
  | ⟨27,_⟩ => exact repair12286Cell27
  | ⟨28,_⟩ => exact repair12286Cell28
  | ⟨29,_⟩ => exact repair12286Cell29
  | ⟨30,_⟩ => exact repair12286Cell30
  | ⟨31,_⟩ => exact repair12286Cell31
  | ⟨32,_⟩ => exact repair12286Cell32
  | ⟨33,_⟩ => exact repair12286Cell33
  | ⟨34,_⟩ => exact repair12286Cell34
  | ⟨35,_⟩ => exact repair12286Cell35
  | ⟨36,_⟩ => exact repair12286Cell36
  | ⟨37,_⟩ => exact repair12286Cell37
  | ⟨38,_⟩ => exact repair12286Cell38
  | ⟨39,_⟩ => exact repair12286Cell39
  | ⟨40,_⟩ => exact repair12286Cell40
  | ⟨41,_⟩ => exact repair12286Cell41
  | ⟨42,_⟩ => exact repair12286Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12286 : FrameRepair 12286 scalarRow12286 where
  cap := cap12286
  cap_nonneg := fun j => (repair12286Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12286])
  endpoint := fun j => (repair12286Cells j).2.1
  endpoint_upper := fun j => (repair12286Cells j).2.2.1
  frame := fun j => (repair12286Cells j).2.2.2

noncomputable def cap12287 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275948037 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138175453 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276752781 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138576829 / 500000000 : ℝ)
  | ⟨4,_⟩ => (34694193 / 125000000 : ℝ)
  | ⟨5,_⟩ => (277952441 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278349877 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278746807 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (6978569 / 25000000 : ℝ)
  | ⟨9,_⟩ => (139768871 / 500000000 : ℝ)
  | ⟨10,_⟩ => (34991469 / 125000000 : ℝ)
  | ⟨11,_⟩ => (140162157 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280716399 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70276759 / 250000000 : ℝ)
  | ⟨14,_⟩ => (140748803 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281887077 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (70568901 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282663201 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283049857 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141717793 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283820387 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (17762767 / 62500000 : ℝ)
  | ⟨22,_⟩ => (8893351 / 31250000 : ℝ)
  | ⟨23,_⟩ => (142484391 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285349919 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (57145939 / 200000000 : ℝ)
  | ⟨26,_⟩ => (286109067 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286487039 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143432057 / 500000000 : ℝ)
  | ⟨29,_⟩ => (143620147 / 500000000 : ℝ)
  | ⟨30,_⟩ => (7190377 / 25000000 : ℝ)
  | ⟨31,_⟩ => (143994741 / 500000000 : ℝ)
  | ⟨32,_⟩ => (144181501 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288735133 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72276597 / 250000000 : ℝ)
  | ⟨35,_⟩ => (72369193 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289846279 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145107463 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72645677 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145474559 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291314669 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (36459921 / 125000000 : ℝ)
  | ⟨42,_⟩ => (58408643 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12287Cell0 :
    0 ≤ cap12287 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨0,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12287 ⟨0,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨0,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell1 :
    0 ≤ cap12287 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨1,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12287 ⟨1,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨1,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell2 :
    0 ≤ cap12287 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨2,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12287 ⟨2,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨2,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell3 :
    0 ≤ cap12287 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨3,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12287 ⟨3,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨3,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell4 :
    0 ≤ cap12287 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨4,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12287 ⟨4,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨4,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell5 :
    0 ≤ cap12287 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨5,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12287 ⟨5,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨5,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell6 :
    0 ≤ cap12287 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨6,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12287 ⟨6,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨6,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell7 :
    0 ≤ cap12287 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨7,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12287 ⟨7,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨7,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell8 :
    0 ≤ cap12287 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨8,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12287 ⟨8,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨8,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell9 :
    0 ≤ cap12287 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨9,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12287 ⟨9,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨9,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell10 :
    0 ≤ cap12287 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨10,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12287 ⟨10,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨10,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell11 :
    0 ≤ cap12287 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨11,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12287 ⟨11,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨11,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell12 :
    0 ≤ cap12287 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨12,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12287 ⟨12,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨12,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell13 :
    0 ≤ cap12287 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨13,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12287 ⟨13,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨13,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell14 :
    0 ≤ cap12287 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨14,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12287 ⟨14,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨14,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell15 :
    0 ≤ cap12287 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨15,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12287 ⟨15,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨15,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell16 :
    0 ≤ cap12287 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨16,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12287 ⟨16,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨16,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell17 :
    0 ≤ cap12287 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨17,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12287 ⟨17,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨17,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell18 :
    0 ≤ cap12287 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨18,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12287 ⟨18,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨18,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell19 :
    0 ≤ cap12287 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨19,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12287 ⟨19,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨19,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell20 :
    0 ≤ cap12287 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨20,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12287 ⟨20,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨20,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell21 :
    0 ≤ cap12287 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨21,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12287 ⟨21,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨21,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell22 :
    0 ≤ cap12287 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨22,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12287 ⟨22,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨22,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell23 :
    0 ≤ cap12287 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨23,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12287 ⟨23,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨23,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell24 :
    0 ≤ cap12287 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨24,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12287 ⟨24,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨24,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell25 :
    0 ≤ cap12287 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨25,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12287 ⟨25,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨25,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell26 :
    0 ≤ cap12287 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨26,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12287 ⟨26,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨26,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell27 :
    0 ≤ cap12287 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨27,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12287 ⟨27,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨27,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell28 :
    0 ≤ cap12287 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨28,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12287 ⟨28,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨28,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell29 :
    0 ≤ cap12287 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨29,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12287 ⟨29,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨29,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell30 :
    0 ≤ cap12287 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨30,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12287 ⟨30,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨30,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell31 :
    0 ≤ cap12287 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨31,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12287 ⟨31,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨31,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell32 :
    0 ≤ cap12287 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨32,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12287 ⟨32,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨32,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell33 :
    0 ≤ cap12287 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨33,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12287 ⟨33,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨33,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell34 :
    0 ≤ cap12287 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨34,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12287 ⟨34,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨34,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell35 :
    0 ≤ cap12287 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨35,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12287 ⟨35,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨35,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell36 :
    0 ≤ cap12287 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨36,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12287 ⟨36,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨36,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell37 :
    0 ≤ cap12287 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨37,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12287 ⟨37,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨37,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell38 :
    0 ≤ cap12287 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨38,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12287 ⟨38,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨38,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell39 :
    0 ≤ cap12287 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨39,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12287 ⟨39,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨39,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell40 :
    0 ≤ cap12287 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨40,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12287 ⟨40,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨40,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell41 :
    0 ≤ cap12287 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨41,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12287 ⟨41,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨41,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cell42 :
    0 ≤ cap12287 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12287 (parameters ⟨42,by decide⟩)
      (scalarRow12287.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12287 ⟨42,by decide⟩ ∧
    (scalarRow12287.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 ⟨42,by decide⟩ + (scalarRow12287.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12287.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12287.targetFrame := by
  norm_num [cap12287, scalarRow12287, sourceIndex, cell12287, BstLean.Part263.envelope, parameters]

theorem repair12287Cells (j : Fin 43) :
    0 ≤ cap12287 j ∧
    BstLean.Part263.envelope 12287 (parameters j) (scalarRow12287.table (sourceIndex j)).upper ≤ cap12287 j ∧
    (scalarRow12287.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12287 j + (scalarRow12287.table (sourceIndex j)).centre) /
      (scalarRow12287.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12287.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12287Cell0
  | ⟨1,_⟩ => exact repair12287Cell1
  | ⟨2,_⟩ => exact repair12287Cell2
  | ⟨3,_⟩ => exact repair12287Cell3
  | ⟨4,_⟩ => exact repair12287Cell4
  | ⟨5,_⟩ => exact repair12287Cell5
  | ⟨6,_⟩ => exact repair12287Cell6
  | ⟨7,_⟩ => exact repair12287Cell7
  | ⟨8,_⟩ => exact repair12287Cell8
  | ⟨9,_⟩ => exact repair12287Cell9
  | ⟨10,_⟩ => exact repair12287Cell10
  | ⟨11,_⟩ => exact repair12287Cell11
  | ⟨12,_⟩ => exact repair12287Cell12
  | ⟨13,_⟩ => exact repair12287Cell13
  | ⟨14,_⟩ => exact repair12287Cell14
  | ⟨15,_⟩ => exact repair12287Cell15
  | ⟨16,_⟩ => exact repair12287Cell16
  | ⟨17,_⟩ => exact repair12287Cell17
  | ⟨18,_⟩ => exact repair12287Cell18
  | ⟨19,_⟩ => exact repair12287Cell19
  | ⟨20,_⟩ => exact repair12287Cell20
  | ⟨21,_⟩ => exact repair12287Cell21
  | ⟨22,_⟩ => exact repair12287Cell22
  | ⟨23,_⟩ => exact repair12287Cell23
  | ⟨24,_⟩ => exact repair12287Cell24
  | ⟨25,_⟩ => exact repair12287Cell25
  | ⟨26,_⟩ => exact repair12287Cell26
  | ⟨27,_⟩ => exact repair12287Cell27
  | ⟨28,_⟩ => exact repair12287Cell28
  | ⟨29,_⟩ => exact repair12287Cell29
  | ⟨30,_⟩ => exact repair12287Cell30
  | ⟨31,_⟩ => exact repair12287Cell31
  | ⟨32,_⟩ => exact repair12287Cell32
  | ⟨33,_⟩ => exact repair12287Cell33
  | ⟨34,_⟩ => exact repair12287Cell34
  | ⟨35,_⟩ => exact repair12287Cell35
  | ⟨36,_⟩ => exact repair12287Cell36
  | ⟨37,_⟩ => exact repair12287Cell37
  | ⟨38,_⟩ => exact repair12287Cell38
  | ⟨39,_⟩ => exact repair12287Cell39
  | ⟨40,_⟩ => exact repair12287Cell40
  | ⟨41,_⟩ => exact repair12287Cell41
  | ⟨42,_⟩ => exact repair12287Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12287 : FrameRepair 12287 scalarRow12287 where
  cap := cap12287
  cap_nonneg := fun j => (repair12287Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12287])
  endpoint := fun j => (repair12287Cells j).2.1
  endpoint_upper := fun j => (repair12287Cells j).2.2.1
  frame := fun j => (repair12287Cells j).2.2.2

noncomputable def cap12288 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137973981 / 500000000 : ℝ)
  | ⟨1,_⟩ => (34543853 / 125000000 : ℝ)
  | ⟨2,_⟩ => (69188173 / 250000000 : ℝ)
  | ⟨3,_⟩ => (277153563 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277553443 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138976167 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278349763 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139373343 / 500000000 : ℝ)
  | ⟨8,_⟩ => (139571317 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279537609 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279931613 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280324169 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280716247 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140553439 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140748721 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140943453 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282275427 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282663017 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283049667 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (28343539 / 100000000 : ℝ)
  | ⟨20,_⟩ => (35477523 / 125000000 : ℝ)
  | ⟨21,_⟩ => (284204063 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284587017 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284968561 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71337423 / 250000000 : ℝ)
  | ⟨25,_⟩ => (142864731 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286108827 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286486793 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143431931 / 500000000 : ℝ)
  | ⟨29,_⟩ => (71810009 / 250000000 : ℝ)
  | ⟨30,_⟩ => (8987963 / 31250000 : ℝ)
  | ⟨31,_⟩ => (71997303 / 250000000 : ℝ)
  | ⟨32,_⟩ => (144181363 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288734851 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (2891061 / 10000000 : ℝ)
  | ⟨35,_⟩ => (144738239 / 500000000 : ℝ)
  | ⟨36,_⟩ => (144922989 / 500000000 : ℝ)
  | ⟨37,_⟩ => (14510731 / 50000000 : ℝ)
  | ⟨38,_⟩ => (72645599 / 250000000 : ℝ)
  | ⟨39,_⟩ => (181843 / 625000 : ℝ)
  | ⟨40,_⟩ => (58262869 / 200000000 : ℝ)
  | ⟨41,_⟩ => (145839519 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292042879 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12288Cell0 :
    0 ≤ cap12288 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨0,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12288 ⟨0,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨0,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell1 :
    0 ≤ cap12288 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨1,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12288 ⟨1,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨1,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell2 :
    0 ≤ cap12288 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨2,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12288 ⟨2,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨2,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell3 :
    0 ≤ cap12288 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨3,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12288 ⟨3,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨3,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell4 :
    0 ≤ cap12288 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨4,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12288 ⟨4,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨4,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell5 :
    0 ≤ cap12288 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨5,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12288 ⟨5,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨5,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell6 :
    0 ≤ cap12288 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨6,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12288 ⟨6,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨6,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell7 :
    0 ≤ cap12288 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨7,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12288 ⟨7,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨7,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell8 :
    0 ≤ cap12288 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨8,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12288 ⟨8,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨8,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell9 :
    0 ≤ cap12288 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨9,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12288 ⟨9,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨9,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell10 :
    0 ≤ cap12288 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨10,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12288 ⟨10,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨10,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell11 :
    0 ≤ cap12288 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨11,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12288 ⟨11,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨11,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell12 :
    0 ≤ cap12288 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨12,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12288 ⟨12,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨12,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell13 :
    0 ≤ cap12288 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨13,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12288 ⟨13,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨13,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell14 :
    0 ≤ cap12288 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨14,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12288 ⟨14,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨14,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell15 :
    0 ≤ cap12288 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨15,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12288 ⟨15,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨15,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell16 :
    0 ≤ cap12288 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨16,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12288 ⟨16,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨16,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell17 :
    0 ≤ cap12288 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨17,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12288 ⟨17,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨17,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell18 :
    0 ≤ cap12288 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨18,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12288 ⟨18,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨18,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell19 :
    0 ≤ cap12288 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨19,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12288 ⟨19,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨19,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell20 :
    0 ≤ cap12288 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨20,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12288 ⟨20,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨20,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell21 :
    0 ≤ cap12288 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨21,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12288 ⟨21,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨21,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell22 :
    0 ≤ cap12288 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨22,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12288 ⟨22,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨22,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell23 :
    0 ≤ cap12288 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨23,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12288 ⟨23,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨23,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell24 :
    0 ≤ cap12288 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨24,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12288 ⟨24,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨24,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell25 :
    0 ≤ cap12288 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨25,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12288 ⟨25,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨25,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell26 :
    0 ≤ cap12288 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨26,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12288 ⟨26,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨26,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell27 :
    0 ≤ cap12288 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨27,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12288 ⟨27,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨27,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell28 :
    0 ≤ cap12288 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨28,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12288 ⟨28,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨28,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell29 :
    0 ≤ cap12288 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨29,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12288 ⟨29,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨29,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell30 :
    0 ≤ cap12288 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨30,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12288 ⟨30,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨30,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell31 :
    0 ≤ cap12288 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨31,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12288 ⟨31,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨31,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell32 :
    0 ≤ cap12288 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨32,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12288 ⟨32,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨32,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell33 :
    0 ≤ cap12288 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨33,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12288 ⟨33,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨33,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell34 :
    0 ≤ cap12288 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨34,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12288 ⟨34,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨34,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell35 :
    0 ≤ cap12288 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨35,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12288 ⟨35,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨35,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell36 :
    0 ≤ cap12288 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨36,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12288 ⟨36,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨36,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell37 :
    0 ≤ cap12288 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨37,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12288 ⟨37,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨37,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell38 :
    0 ≤ cap12288 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨38,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12288 ⟨38,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨38,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell39 :
    0 ≤ cap12288 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨39,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12288 ⟨39,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨39,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell40 :
    0 ≤ cap12288 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨40,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12288 ⟨40,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨40,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell41 :
    0 ≤ cap12288 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨41,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12288 ⟨41,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨41,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cell42 :
    0 ≤ cap12288 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12288 (parameters ⟨42,by decide⟩)
      (scalarRow12288.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12288 ⟨42,by decide⟩ ∧
    (scalarRow12288.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 ⟨42,by decide⟩ + (scalarRow12288.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12288.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12288.targetFrame := by
  norm_num [cap12288, scalarRow12288, sourceIndex, cell12288, BstLean.Part263.envelope, parameters]

theorem repair12288Cells (j : Fin 43) :
    0 ≤ cap12288 j ∧
    BstLean.Part263.envelope 12288 (parameters j) (scalarRow12288.table (sourceIndex j)).upper ≤ cap12288 j ∧
    (scalarRow12288.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12288 j + (scalarRow12288.table (sourceIndex j)).centre) /
      (scalarRow12288.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12288.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12288Cell0
  | ⟨1,_⟩ => exact repair12288Cell1
  | ⟨2,_⟩ => exact repair12288Cell2
  | ⟨3,_⟩ => exact repair12288Cell3
  | ⟨4,_⟩ => exact repair12288Cell4
  | ⟨5,_⟩ => exact repair12288Cell5
  | ⟨6,_⟩ => exact repair12288Cell6
  | ⟨7,_⟩ => exact repair12288Cell7
  | ⟨8,_⟩ => exact repair12288Cell8
  | ⟨9,_⟩ => exact repair12288Cell9
  | ⟨10,_⟩ => exact repair12288Cell10
  | ⟨11,_⟩ => exact repair12288Cell11
  | ⟨12,_⟩ => exact repair12288Cell12
  | ⟨13,_⟩ => exact repair12288Cell13
  | ⟨14,_⟩ => exact repair12288Cell14
  | ⟨15,_⟩ => exact repair12288Cell15
  | ⟨16,_⟩ => exact repair12288Cell16
  | ⟨17,_⟩ => exact repair12288Cell17
  | ⟨18,_⟩ => exact repair12288Cell18
  | ⟨19,_⟩ => exact repair12288Cell19
  | ⟨20,_⟩ => exact repair12288Cell20
  | ⟨21,_⟩ => exact repair12288Cell21
  | ⟨22,_⟩ => exact repair12288Cell22
  | ⟨23,_⟩ => exact repair12288Cell23
  | ⟨24,_⟩ => exact repair12288Cell24
  | ⟨25,_⟩ => exact repair12288Cell25
  | ⟨26,_⟩ => exact repair12288Cell26
  | ⟨27,_⟩ => exact repair12288Cell27
  | ⟨28,_⟩ => exact repair12288Cell28
  | ⟨29,_⟩ => exact repair12288Cell29
  | ⟨30,_⟩ => exact repair12288Cell30
  | ⟨31,_⟩ => exact repair12288Cell31
  | ⟨32,_⟩ => exact repair12288Cell32
  | ⟨33,_⟩ => exact repair12288Cell33
  | ⟨34,_⟩ => exact repair12288Cell34
  | ⟨35,_⟩ => exact repair12288Cell35
  | ⟨36,_⟩ => exact repair12288Cell36
  | ⟨37,_⟩ => exact repair12288Cell37
  | ⟨38,_⟩ => exact repair12288Cell38
  | ⟨39,_⟩ => exact repair12288Cell39
  | ⟨40,_⟩ => exact repair12288Cell40
  | ⟨41,_⟩ => exact repair12288Cell41
  | ⟨42,_⟩ => exact repair12288Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12288 : FrameRepair 12288 scalarRow12288 where
  cap := cap12288
  cap_nonneg := fun j => (repair12288Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12288])
  endpoint := fun j => (repair12288Cells j).2.1
  endpoint_upper := fun j => (repair12288Cells j).2.2.1
  frame := fun j => (repair12288Cells j).2.2.2

noncomputable def cap12289 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137973943 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138175371 / 500000000 : ℝ)
  | ⟨2,_⟩ => (69188151 / 250000000 : ℝ)
  | ⟨3,_⟩ => (69288367 / 250000000 : ℝ)
  | ⟨4,_⟩ => (138776671 / 500000000 : ℝ)
  | ⟨5,_⟩ => (138976113 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278349649 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139373283 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279142507 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (11181499 / 40000000 : ℝ)
  | ⟨10,_⟩ => (279931473 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280324023 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140358047 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281106719 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281497277 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140943367 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282275249 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282662833 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283049477 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283435193 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141909991 / 500000000 : ℝ)
  | ⟨21,_⟩ => (142101927 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284586803 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (14248417 / 50000000 : ℝ)
  | ⟨24,_⟩ => (57069893 / 200000000 : ℝ)
  | ⟨25,_⟩ => (285729229 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (71527147 / 250000000 : ℝ)
  | ⟨27,_⟩ => (286486547 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286863611 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143619889 / 500000000 : ℝ)
  | ⟨30,_⟩ => (35951819 / 125000000 : ℝ)
  | ⟨31,_⟩ => (143994471 / 500000000 : ℝ)
  | ⟨32,_⟩ => (5767249 / 20000000 : ℝ)
  | ⟨33,_⟩ => (288734569 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72276453 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289476183 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144922839 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145107157 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72645521 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145474241 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291314021 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (72919677 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292042543 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12289Cell0 :
    0 ≤ cap12289 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨0,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12289 ⟨0,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨0,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell1 :
    0 ≤ cap12289 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨1,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12289 ⟨1,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨1,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell2 :
    0 ≤ cap12289 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨2,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12289 ⟨2,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨2,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell3 :
    0 ≤ cap12289 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨3,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12289 ⟨3,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨3,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell4 :
    0 ≤ cap12289 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨4,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12289 ⟨4,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨4,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell5 :
    0 ≤ cap12289 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨5,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12289 ⟨5,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨5,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell6 :
    0 ≤ cap12289 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨6,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12289 ⟨6,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨6,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell7 :
    0 ≤ cap12289 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨7,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12289 ⟨7,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨7,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell8 :
    0 ≤ cap12289 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨8,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12289 ⟨8,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨8,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell9 :
    0 ≤ cap12289 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨9,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12289 ⟨9,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨9,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell10 :
    0 ≤ cap12289 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨10,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12289 ⟨10,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨10,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell11 :
    0 ≤ cap12289 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨11,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12289 ⟨11,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨11,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell12 :
    0 ≤ cap12289 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨12,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12289 ⟨12,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨12,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell13 :
    0 ≤ cap12289 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨13,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12289 ⟨13,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨13,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell14 :
    0 ≤ cap12289 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨14,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12289 ⟨14,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨14,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell15 :
    0 ≤ cap12289 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨15,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12289 ⟨15,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨15,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell16 :
    0 ≤ cap12289 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨16,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12289 ⟨16,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨16,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell17 :
    0 ≤ cap12289 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨17,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12289 ⟨17,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨17,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell18 :
    0 ≤ cap12289 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨18,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12289 ⟨18,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨18,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell19 :
    0 ≤ cap12289 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨19,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12289 ⟨19,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨19,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell20 :
    0 ≤ cap12289 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨20,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12289 ⟨20,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨20,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell21 :
    0 ≤ cap12289 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨21,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12289 ⟨21,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨21,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell22 :
    0 ≤ cap12289 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨22,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12289 ⟨22,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨22,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell23 :
    0 ≤ cap12289 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨23,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12289 ⟨23,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨23,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell24 :
    0 ≤ cap12289 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨24,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12289 ⟨24,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨24,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell25 :
    0 ≤ cap12289 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨25,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12289 ⟨25,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨25,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell26 :
    0 ≤ cap12289 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨26,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12289 ⟨26,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨26,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell27 :
    0 ≤ cap12289 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨27,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12289 ⟨27,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨27,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell28 :
    0 ≤ cap12289 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨28,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12289 ⟨28,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨28,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell29 :
    0 ≤ cap12289 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨29,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12289 ⟨29,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨29,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell30 :
    0 ≤ cap12289 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨30,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12289 ⟨30,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨30,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell31 :
    0 ≤ cap12289 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨31,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12289 ⟨31,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨31,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell32 :
    0 ≤ cap12289 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨32,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12289 ⟨32,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨32,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell33 :
    0 ≤ cap12289 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨33,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12289 ⟨33,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨33,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell34 :
    0 ≤ cap12289 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨34,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12289 ⟨34,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨34,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell35 :
    0 ≤ cap12289 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨35,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12289 ⟨35,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨35,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell36 :
    0 ≤ cap12289 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨36,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12289 ⟨36,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨36,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell37 :
    0 ≤ cap12289 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨37,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12289 ⟨37,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨37,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell38 :
    0 ≤ cap12289 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨38,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12289 ⟨38,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨38,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell39 :
    0 ≤ cap12289 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨39,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12289 ⟨39,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨39,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell40 :
    0 ≤ cap12289 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨40,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12289 ⟨40,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨40,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell41 :
    0 ≤ cap12289 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨41,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12289 ⟨41,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨41,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cell42 :
    0 ≤ cap12289 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12289 (parameters ⟨42,by decide⟩)
      (scalarRow12289.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12289 ⟨42,by decide⟩ ∧
    (scalarRow12289.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 ⟨42,by decide⟩ + (scalarRow12289.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12289.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12289.targetFrame := by
  norm_num [cap12289, scalarRow12289, sourceIndex, cell12289, BstLean.Part263.envelope, parameters]

theorem repair12289Cells (j : Fin 43) :
    0 ≤ cap12289 j ∧
    BstLean.Part263.envelope 12289 (parameters j) (scalarRow12289.table (sourceIndex j)).upper ≤ cap12289 j ∧
    (scalarRow12289.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12289 j + (scalarRow12289.table (sourceIndex j)).centre) /
      (scalarRow12289.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12289.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12289Cell0
  | ⟨1,_⟩ => exact repair12289Cell1
  | ⟨2,_⟩ => exact repair12289Cell2
  | ⟨3,_⟩ => exact repair12289Cell3
  | ⟨4,_⟩ => exact repair12289Cell4
  | ⟨5,_⟩ => exact repair12289Cell5
  | ⟨6,_⟩ => exact repair12289Cell6
  | ⟨7,_⟩ => exact repair12289Cell7
  | ⟨8,_⟩ => exact repair12289Cell8
  | ⟨9,_⟩ => exact repair12289Cell9
  | ⟨10,_⟩ => exact repair12289Cell10
  | ⟨11,_⟩ => exact repair12289Cell11
  | ⟨12,_⟩ => exact repair12289Cell12
  | ⟨13,_⟩ => exact repair12289Cell13
  | ⟨14,_⟩ => exact repair12289Cell14
  | ⟨15,_⟩ => exact repair12289Cell15
  | ⟨16,_⟩ => exact repair12289Cell16
  | ⟨17,_⟩ => exact repair12289Cell17
  | ⟨18,_⟩ => exact repair12289Cell18
  | ⟨19,_⟩ => exact repair12289Cell19
  | ⟨20,_⟩ => exact repair12289Cell20
  | ⟨21,_⟩ => exact repair12289Cell21
  | ⟨22,_⟩ => exact repair12289Cell22
  | ⟨23,_⟩ => exact repair12289Cell23
  | ⟨24,_⟩ => exact repair12289Cell24
  | ⟨25,_⟩ => exact repair12289Cell25
  | ⟨26,_⟩ => exact repair12289Cell26
  | ⟨27,_⟩ => exact repair12289Cell27
  | ⟨28,_⟩ => exact repair12289Cell28
  | ⟨29,_⟩ => exact repair12289Cell29
  | ⟨30,_⟩ => exact repair12289Cell30
  | ⟨31,_⟩ => exact repair12289Cell31
  | ⟨32,_⟩ => exact repair12289Cell32
  | ⟨33,_⟩ => exact repair12289Cell33
  | ⟨34,_⟩ => exact repair12289Cell34
  | ⟨35,_⟩ => exact repair12289Cell35
  | ⟨36,_⟩ => exact repair12289Cell36
  | ⟨37,_⟩ => exact repair12289Cell37
  | ⟨38,_⟩ => exact repair12289Cell38
  | ⟨39,_⟩ => exact repair12289Cell39
  | ⟨40,_⟩ => exact repair12289Cell40
  | ⟨41,_⟩ => exact repair12289Cell41
  | ⟨42,_⟩ => exact repair12289Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12289 : FrameRepair 12289 scalarRow12289 where
  cap := cap12289
  cap_nonneg := fun j => (repair12289Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12289])
  endpoint := fun j => (repair12289Cells j).2.1
  endpoint_upper := fun j => (repair12289Cells j).2.2.1
  frame := fun j => (repair12289Cells j).2.2.2

noncomputable def cap12290 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275947811 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (13817533 / 50000000 : ℝ)
  | ⟨2,_⟩ => (69188129 / 250000000 : ℝ)
  | ⟨3,_⟩ => (277153373 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277553241 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138976059 / 500000000 : ℝ)
  | ⟨6,_⟩ => (55669907 / 200000000 : ℝ)
  | ⟨7,_⟩ => (55749289 / 200000000 : ℝ)
  | ⟨8,_⟩ => (13957119 / 50000000 : ℝ)
  | ⟨9,_⟩ => (139768671 / 500000000 : ℝ)
  | ⟨10,_⟩ => (139965667 / 500000000 : ℝ)
  | ⟨11,_⟩ => (280323877 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140357971 / 500000000 : ℝ)
  | ⟨13,_⟩ => (439229 / 1562500 : ℝ)
  | ⟨14,_⟩ => (35187139 / 125000000 : ℝ)
  | ⟨15,_⟩ => (281886563 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (1102637 / 3906250 : ℝ)
  | ⟨17,_⟩ => (282662649 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (35381161 / 125000000 : ℝ)
  | ⟨19,_⟩ => (283434997 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (14190989 / 50000000 : ℝ)
  | ⟨21,_⟩ => (142101823 / 500000000 : ℝ)
  | ⟨22,_⟩ => (71146647 / 250000000 : ℝ)
  | ⟨23,_⟩ => (284968119 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142674619 / 500000000 : ℝ)
  | ⟨25,_⟩ => (57145799 / 200000000 : ℝ)
  | ⟨26,_⟩ => (71527087 / 250000000 : ℝ)
  | ⟨27,_⟩ => (143243151 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286863359 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (1795247 / 6250000 : ℝ)
  | ⟨30,_⟩ => (17975893 / 62500000 : ℝ)
  | ⟨31,_⟩ => (4499823 / 15625000 : ℝ)
  | ⟨32,_⟩ => (144181087 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288734287 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72276381 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289475889 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144922689 / 500000000 : ℝ)
  | ⟨37,_⟩ => (36276751 / 125000000 : ℝ)
  | ⟨38,_⟩ => (72645443 / 250000000 : ℝ)
  | ⟨39,_⟩ => (72737041 / 250000000 : ℝ)
  | ⟨40,_⟩ => (291313697 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145839189 / 500000000 : ℝ)
  | ⟨42,_⟩ => (9126319 / 31250000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12290Cell0 :
    0 ≤ cap12290 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨0,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12290 ⟨0,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨0,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell1 :
    0 ≤ cap12290 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨1,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12290 ⟨1,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨1,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell2 :
    0 ≤ cap12290 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨2,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12290 ⟨2,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨2,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell3 :
    0 ≤ cap12290 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨3,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12290 ⟨3,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨3,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell4 :
    0 ≤ cap12290 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨4,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12290 ⟨4,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨4,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell5 :
    0 ≤ cap12290 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨5,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12290 ⟨5,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨5,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell6 :
    0 ≤ cap12290 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨6,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12290 ⟨6,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨6,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell7 :
    0 ≤ cap12290 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨7,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12290 ⟨7,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨7,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell8 :
    0 ≤ cap12290 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨8,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12290 ⟨8,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨8,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell9 :
    0 ≤ cap12290 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨9,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12290 ⟨9,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨9,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell10 :
    0 ≤ cap12290 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨10,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12290 ⟨10,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨10,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell11 :
    0 ≤ cap12290 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨11,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12290 ⟨11,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨11,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell12 :
    0 ≤ cap12290 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨12,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12290 ⟨12,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨12,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell13 :
    0 ≤ cap12290 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨13,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12290 ⟨13,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨13,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell14 :
    0 ≤ cap12290 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨14,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12290 ⟨14,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨14,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell15 :
    0 ≤ cap12290 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨15,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12290 ⟨15,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨15,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell16 :
    0 ≤ cap12290 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨16,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12290 ⟨16,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨16,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell17 :
    0 ≤ cap12290 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨17,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12290 ⟨17,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨17,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell18 :
    0 ≤ cap12290 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨18,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12290 ⟨18,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨18,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell19 :
    0 ≤ cap12290 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨19,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12290 ⟨19,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨19,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell20 :
    0 ≤ cap12290 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨20,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12290 ⟨20,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨20,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell21 :
    0 ≤ cap12290 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨21,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12290 ⟨21,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨21,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell22 :
    0 ≤ cap12290 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨22,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12290 ⟨22,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨22,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell23 :
    0 ≤ cap12290 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨23,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12290 ⟨23,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨23,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell24 :
    0 ≤ cap12290 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨24,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12290 ⟨24,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨24,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell25 :
    0 ≤ cap12290 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨25,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12290 ⟨25,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨25,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell26 :
    0 ≤ cap12290 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨26,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12290 ⟨26,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨26,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell27 :
    0 ≤ cap12290 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨27,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12290 ⟨27,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨27,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell28 :
    0 ≤ cap12290 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨28,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12290 ⟨28,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨28,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell29 :
    0 ≤ cap12290 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨29,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12290 ⟨29,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨29,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell30 :
    0 ≤ cap12290 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨30,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12290 ⟨30,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨30,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell31 :
    0 ≤ cap12290 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨31,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12290 ⟨31,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨31,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell32 :
    0 ≤ cap12290 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨32,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12290 ⟨32,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨32,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell33 :
    0 ≤ cap12290 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨33,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12290 ⟨33,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨33,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell34 :
    0 ≤ cap12290 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨34,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12290 ⟨34,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨34,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell35 :
    0 ≤ cap12290 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨35,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12290 ⟨35,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨35,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell36 :
    0 ≤ cap12290 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨36,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12290 ⟨36,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨36,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell37 :
    0 ≤ cap12290 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨37,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12290 ⟨37,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨37,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell38 :
    0 ≤ cap12290 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨38,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12290 ⟨38,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨38,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell39 :
    0 ≤ cap12290 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨39,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12290 ⟨39,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨39,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell40 :
    0 ≤ cap12290 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨40,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12290 ⟨40,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨40,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell41 :
    0 ≤ cap12290 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨41,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12290 ⟨41,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨41,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cell42 :
    0 ≤ cap12290 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12290 (parameters ⟨42,by decide⟩)
      (scalarRow12290.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12290 ⟨42,by decide⟩ ∧
    (scalarRow12290.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 ⟨42,by decide⟩ + (scalarRow12290.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12290.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12290.targetFrame := by
  norm_num [cap12290, scalarRow12290, sourceIndex, cell12290, BstLean.Part263.envelope, parameters]

theorem repair12290Cells (j : Fin 43) :
    0 ≤ cap12290 j ∧
    BstLean.Part263.envelope 12290 (parameters j) (scalarRow12290.table (sourceIndex j)).upper ≤ cap12290 j ∧
    (scalarRow12290.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12290 j + (scalarRow12290.table (sourceIndex j)).centre) /
      (scalarRow12290.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12290.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12290Cell0
  | ⟨1,_⟩ => exact repair12290Cell1
  | ⟨2,_⟩ => exact repair12290Cell2
  | ⟨3,_⟩ => exact repair12290Cell3
  | ⟨4,_⟩ => exact repair12290Cell4
  | ⟨5,_⟩ => exact repair12290Cell5
  | ⟨6,_⟩ => exact repair12290Cell6
  | ⟨7,_⟩ => exact repair12290Cell7
  | ⟨8,_⟩ => exact repair12290Cell8
  | ⟨9,_⟩ => exact repair12290Cell9
  | ⟨10,_⟩ => exact repair12290Cell10
  | ⟨11,_⟩ => exact repair12290Cell11
  | ⟨12,_⟩ => exact repair12290Cell12
  | ⟨13,_⟩ => exact repair12290Cell13
  | ⟨14,_⟩ => exact repair12290Cell14
  | ⟨15,_⟩ => exact repair12290Cell15
  | ⟨16,_⟩ => exact repair12290Cell16
  | ⟨17,_⟩ => exact repair12290Cell17
  | ⟨18,_⟩ => exact repair12290Cell18
  | ⟨19,_⟩ => exact repair12290Cell19
  | ⟨20,_⟩ => exact repair12290Cell20
  | ⟨21,_⟩ => exact repair12290Cell21
  | ⟨22,_⟩ => exact repair12290Cell22
  | ⟨23,_⟩ => exact repair12290Cell23
  | ⟨24,_⟩ => exact repair12290Cell24
  | ⟨25,_⟩ => exact repair12290Cell25
  | ⟨26,_⟩ => exact repair12290Cell26
  | ⟨27,_⟩ => exact repair12290Cell27
  | ⟨28,_⟩ => exact repair12290Cell28
  | ⟨29,_⟩ => exact repair12290Cell29
  | ⟨30,_⟩ => exact repair12290Cell30
  | ⟨31,_⟩ => exact repair12290Cell31
  | ⟨32,_⟩ => exact repair12290Cell32
  | ⟨33,_⟩ => exact repair12290Cell33
  | ⟨34,_⟩ => exact repair12290Cell34
  | ⟨35,_⟩ => exact repair12290Cell35
  | ⟨36,_⟩ => exact repair12290Cell36
  | ⟨37,_⟩ => exact repair12290Cell37
  | ⟨38,_⟩ => exact repair12290Cell38
  | ⟨39,_⟩ => exact repair12290Cell39
  | ⟨40,_⟩ => exact repair12290Cell40
  | ⟨41,_⟩ => exact repair12290Cell41
  | ⟨42,_⟩ => exact repair12290Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12290 : FrameRepair 12290 scalarRow12290 where
  cap := cap12290
  cap_nonneg := fun j => (repair12290Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12290])
  endpoint := fun j => (repair12290Cells j).2.1
  endpoint_upper := fun j => (repair12290Cells j).2.2.1
  frame := fun j => (repair12290Cells j).2.2.2

noncomputable def cap12291 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55189547 / 200000000 : ℝ)
  | ⟨1,_⟩ => (276350579 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276752427 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277153279 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277553139 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277952011 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278349421 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (11149853 / 40000000 : ℝ)
  | ⟨8,_⟩ => (279142253 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279537209 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (139965597 / 500000000 : ℝ)
  | ⟨11,_⟩ => (280323731 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (28071579 / 100000000 : ℝ)
  | ⟨13,_⟩ => (140553201 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281496947 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (35235799 / 125000000 : ℝ)
  | ⟨16,_⟩ => (56454979 / 200000000 : ℝ)
  | ⟨17,_⟩ => (141331233 / 500000000 : ℝ)
  | ⟨18,_⟩ => (141524549 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283434801 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283819577 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284203437 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284586373 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142483949 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285349011 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142864381 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286108109 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (35810757 / 125000000 : ℝ)
  | ⟨28,_⟩ => (286863107 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287239263 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (35951753 / 125000000 : ℝ)
  | ⟨31,_⟩ => (143994201 / 500000000 : ℝ)
  | ⟨32,_⟩ => (144180949 / 500000000 : ℝ)
  | ⟨33,_⟩ => (57746801 / 200000000 : ℝ)
  | ⟨34,_⟩ => (72276309 / 250000000 : ℝ)
  | ⟨35,_⟩ => (57895119 / 200000000 : ℝ)
  | ⟨36,_⟩ => (144922539 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145106851 / 500000000 : ℝ)
  | ⟨38,_⟩ => (14529073 / 50000000 : ℝ)
  | ⟨39,_⟩ => (145473923 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291313373 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (9114939 / 31250000 : ℝ)
  | ⟨42,_⟩ => (18252617 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12291Cell0 :
    0 ≤ cap12291 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨0,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12291 ⟨0,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨0,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell1 :
    0 ≤ cap12291 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨1,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12291 ⟨1,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨1,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell2 :
    0 ≤ cap12291 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨2,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12291 ⟨2,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨2,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell3 :
    0 ≤ cap12291 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨3,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12291 ⟨3,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨3,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell4 :
    0 ≤ cap12291 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨4,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12291 ⟨4,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨4,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell5 :
    0 ≤ cap12291 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨5,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12291 ⟨5,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨5,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell6 :
    0 ≤ cap12291 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨6,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12291 ⟨6,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨6,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell7 :
    0 ≤ cap12291 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨7,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12291 ⟨7,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨7,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell8 :
    0 ≤ cap12291 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨8,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12291 ⟨8,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨8,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell9 :
    0 ≤ cap12291 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨9,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12291 ⟨9,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨9,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell10 :
    0 ≤ cap12291 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨10,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12291 ⟨10,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨10,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell11 :
    0 ≤ cap12291 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨11,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12291 ⟨11,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨11,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell12 :
    0 ≤ cap12291 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨12,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12291 ⟨12,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨12,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell13 :
    0 ≤ cap12291 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨13,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12291 ⟨13,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨13,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell14 :
    0 ≤ cap12291 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨14,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12291 ⟨14,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨14,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell15 :
    0 ≤ cap12291 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨15,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12291 ⟨15,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨15,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell16 :
    0 ≤ cap12291 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨16,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12291 ⟨16,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨16,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell17 :
    0 ≤ cap12291 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨17,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12291 ⟨17,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨17,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell18 :
    0 ≤ cap12291 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨18,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12291 ⟨18,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨18,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell19 :
    0 ≤ cap12291 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨19,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12291 ⟨19,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨19,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell20 :
    0 ≤ cap12291 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨20,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12291 ⟨20,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨20,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell21 :
    0 ≤ cap12291 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨21,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12291 ⟨21,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨21,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell22 :
    0 ≤ cap12291 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨22,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12291 ⟨22,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨22,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell23 :
    0 ≤ cap12291 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨23,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12291 ⟨23,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨23,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell24 :
    0 ≤ cap12291 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨24,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12291 ⟨24,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨24,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell25 :
    0 ≤ cap12291 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨25,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12291 ⟨25,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨25,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell26 :
    0 ≤ cap12291 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨26,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12291 ⟨26,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨26,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell27 :
    0 ≤ cap12291 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨27,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12291 ⟨27,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨27,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell28 :
    0 ≤ cap12291 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨28,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12291 ⟨28,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨28,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell29 :
    0 ≤ cap12291 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨29,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12291 ⟨29,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨29,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell30 :
    0 ≤ cap12291 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨30,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12291 ⟨30,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨30,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell31 :
    0 ≤ cap12291 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨31,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12291 ⟨31,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨31,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell32 :
    0 ≤ cap12291 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨32,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12291 ⟨32,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨32,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell33 :
    0 ≤ cap12291 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨33,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12291 ⟨33,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨33,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell34 :
    0 ≤ cap12291 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨34,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12291 ⟨34,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨34,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell35 :
    0 ≤ cap12291 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨35,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12291 ⟨35,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨35,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell36 :
    0 ≤ cap12291 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨36,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12291 ⟨36,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨36,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell37 :
    0 ≤ cap12291 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨37,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12291 ⟨37,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨37,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell38 :
    0 ≤ cap12291 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨38,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12291 ⟨38,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨38,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell39 :
    0 ≤ cap12291 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨39,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12291 ⟨39,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨39,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell40 :
    0 ≤ cap12291 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨40,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12291 ⟨40,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨40,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell41 :
    0 ≤ cap12291 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨41,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12291 ⟨41,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨41,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cell42 :
    0 ≤ cap12291 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12291 (parameters ⟨42,by decide⟩)
      (scalarRow12291.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12291 ⟨42,by decide⟩ ∧
    (scalarRow12291.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 ⟨42,by decide⟩ + (scalarRow12291.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12291.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12291.targetFrame := by
  norm_num [cap12291, scalarRow12291, sourceIndex, cell12291, BstLean.Part263.envelope, parameters]

theorem repair12291Cells (j : Fin 43) :
    0 ≤ cap12291 j ∧
    BstLean.Part263.envelope 12291 (parameters j) (scalarRow12291.table (sourceIndex j)).upper ≤ cap12291 j ∧
    (scalarRow12291.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12291 j + (scalarRow12291.table (sourceIndex j)).centre) /
      (scalarRow12291.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12291.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12291Cell0
  | ⟨1,_⟩ => exact repair12291Cell1
  | ⟨2,_⟩ => exact repair12291Cell2
  | ⟨3,_⟩ => exact repair12291Cell3
  | ⟨4,_⟩ => exact repair12291Cell4
  | ⟨5,_⟩ => exact repair12291Cell5
  | ⟨6,_⟩ => exact repair12291Cell6
  | ⟨7,_⟩ => exact repair12291Cell7
  | ⟨8,_⟩ => exact repair12291Cell8
  | ⟨9,_⟩ => exact repair12291Cell9
  | ⟨10,_⟩ => exact repair12291Cell10
  | ⟨11,_⟩ => exact repair12291Cell11
  | ⟨12,_⟩ => exact repair12291Cell12
  | ⟨13,_⟩ => exact repair12291Cell13
  | ⟨14,_⟩ => exact repair12291Cell14
  | ⟨15,_⟩ => exact repair12291Cell15
  | ⟨16,_⟩ => exact repair12291Cell16
  | ⟨17,_⟩ => exact repair12291Cell17
  | ⟨18,_⟩ => exact repair12291Cell18
  | ⟨19,_⟩ => exact repair12291Cell19
  | ⟨20,_⟩ => exact repair12291Cell20
  | ⟨21,_⟩ => exact repair12291Cell21
  | ⟨22,_⟩ => exact repair12291Cell22
  | ⟨23,_⟩ => exact repair12291Cell23
  | ⟨24,_⟩ => exact repair12291Cell24
  | ⟨25,_⟩ => exact repair12291Cell25
  | ⟨26,_⟩ => exact repair12291Cell26
  | ⟨27,_⟩ => exact repair12291Cell27
  | ⟨28,_⟩ => exact repair12291Cell28
  | ⟨29,_⟩ => exact repair12291Cell29
  | ⟨30,_⟩ => exact repair12291Cell30
  | ⟨31,_⟩ => exact repair12291Cell31
  | ⟨32,_⟩ => exact repair12291Cell32
  | ⟨33,_⟩ => exact repair12291Cell33
  | ⟨34,_⟩ => exact repair12291Cell34
  | ⟨35,_⟩ => exact repair12291Cell35
  | ⟨36,_⟩ => exact repair12291Cell36
  | ⟨37,_⟩ => exact repair12291Cell37
  | ⟨38,_⟩ => exact repair12291Cell38
  | ⟨39,_⟩ => exact repair12291Cell39
  | ⟨40,_⟩ => exact repair12291Cell40
  | ⟨41,_⟩ => exact repair12291Cell41
  | ⟨42,_⟩ => exact repair12291Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12291 : FrameRepair 12291 scalarRow12291 where
  cap := cap12291
  cap_nonneg := fun j => (repair12291Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12291])
  endpoint := fun j => (repair12291Cells j).2.1
  endpoint_upper := fun j => (repair12291Cells j).2.2.1
  frame := fun j => (repair12291Cells j).2.2.2

noncomputable def cap12292 : Fin 43 → ℝ
  | ⟨0,_⟩ => (13797383 / 50000000 : ℝ)
  | ⟨1,_⟩ => (276350497 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276752339 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (8661037 / 31250000 : ℝ)
  | ⟨4,_⟩ => (138776519 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277951903 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278349307 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (69686551 / 250000000 : ℝ)
  | ⟨8,_⟩ => (139571063 / 500000000 : ℝ)
  | ⟨9,_⟩ => (69884269 / 250000000 : ℝ)
  | ⟨10,_⟩ => (55986211 / 200000000 : ℝ)
  | ⟨11,_⟩ => (56064717 / 200000000 : ℝ)
  | ⟨12,_⟩ => (140357819 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281106243 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140748391 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281886221 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282274717 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141331141 / 500000000 : ℝ)
  | ⟨18,_⟩ => (70762227 / 250000000 : ℝ)
  | ⟨19,_⟩ => (56686921 / 200000000 : ℝ)
  | ⟨20,_⟩ => (454111 / 1600000 : ℝ)
  | ⟨21,_⟩ => (284203229 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142293079 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284967677 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (17834299 / 62500000 : ℝ)
  | ⟨25,_⟩ => (285728529 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (28610787 / 100000000 : ℝ)
  | ⟨27,_⟩ => (286485811 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (35857857 / 125000000 : ℝ)
  | ⟨29,_⟩ => (57447801 / 200000000 : ℝ)
  | ⟨30,_⟩ => (287613761 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (71997033 / 250000000 : ℝ)
  | ⟨32,_⟩ => (144180811 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288733723 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72276237 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289475301 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144922389 / 500000000 : ℝ)
  | ⟨37,_⟩ => (58042679 / 200000000 : ℝ)
  | ⟨38,_⟩ => (72645287 / 250000000 : ℝ)
  | ⟨39,_⟩ => (36368441 / 125000000 : ℝ)
  | ⟨40,_⟩ => (291313049 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145838859 / 500000000 : ℝ)
  | ⟨42,_⟩ => (4563149 / 15625000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12292Cell0 :
    0 ≤ cap12292 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨0,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12292 ⟨0,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨0,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell1 :
    0 ≤ cap12292 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨1,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12292 ⟨1,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨1,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell2 :
    0 ≤ cap12292 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨2,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12292 ⟨2,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨2,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell3 :
    0 ≤ cap12292 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨3,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12292 ⟨3,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨3,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell4 :
    0 ≤ cap12292 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨4,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12292 ⟨4,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨4,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell5 :
    0 ≤ cap12292 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨5,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12292 ⟨5,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨5,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell6 :
    0 ≤ cap12292 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨6,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12292 ⟨6,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨6,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell7 :
    0 ≤ cap12292 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨7,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12292 ⟨7,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨7,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell8 :
    0 ≤ cap12292 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨8,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12292 ⟨8,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨8,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell9 :
    0 ≤ cap12292 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨9,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12292 ⟨9,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨9,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell10 :
    0 ≤ cap12292 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨10,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12292 ⟨10,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨10,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell11 :
    0 ≤ cap12292 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨11,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12292 ⟨11,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨11,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell12 :
    0 ≤ cap12292 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨12,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12292 ⟨12,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨12,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell13 :
    0 ≤ cap12292 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨13,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12292 ⟨13,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨13,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell14 :
    0 ≤ cap12292 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨14,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12292 ⟨14,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨14,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell15 :
    0 ≤ cap12292 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨15,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12292 ⟨15,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨15,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell16 :
    0 ≤ cap12292 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨16,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12292 ⟨16,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨16,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell17 :
    0 ≤ cap12292 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨17,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12292 ⟨17,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨17,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell18 :
    0 ≤ cap12292 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨18,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12292 ⟨18,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨18,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell19 :
    0 ≤ cap12292 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨19,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12292 ⟨19,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨19,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell20 :
    0 ≤ cap12292 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨20,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12292 ⟨20,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨20,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell21 :
    0 ≤ cap12292 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨21,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12292 ⟨21,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨21,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell22 :
    0 ≤ cap12292 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨22,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12292 ⟨22,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨22,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell23 :
    0 ≤ cap12292 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨23,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12292 ⟨23,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨23,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell24 :
    0 ≤ cap12292 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨24,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12292 ⟨24,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨24,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell25 :
    0 ≤ cap12292 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨25,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12292 ⟨25,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨25,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell26 :
    0 ≤ cap12292 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨26,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12292 ⟨26,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨26,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell27 :
    0 ≤ cap12292 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨27,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12292 ⟨27,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨27,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell28 :
    0 ≤ cap12292 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨28,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12292 ⟨28,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨28,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell29 :
    0 ≤ cap12292 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨29,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12292 ⟨29,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨29,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell30 :
    0 ≤ cap12292 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨30,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12292 ⟨30,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨30,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell31 :
    0 ≤ cap12292 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨31,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12292 ⟨31,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨31,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell32 :
    0 ≤ cap12292 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨32,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12292 ⟨32,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨32,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell33 :
    0 ≤ cap12292 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨33,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12292 ⟨33,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨33,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell34 :
    0 ≤ cap12292 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨34,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12292 ⟨34,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨34,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell35 :
    0 ≤ cap12292 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨35,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12292 ⟨35,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨35,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell36 :
    0 ≤ cap12292 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨36,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12292 ⟨36,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨36,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell37 :
    0 ≤ cap12292 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨37,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12292 ⟨37,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨37,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell38 :
    0 ≤ cap12292 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨38,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12292 ⟨38,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨38,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell39 :
    0 ≤ cap12292 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨39,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12292 ⟨39,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨39,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell40 :
    0 ≤ cap12292 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨40,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12292 ⟨40,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨40,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell41 :
    0 ≤ cap12292 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨41,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12292 ⟨41,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨41,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cell42 :
    0 ≤ cap12292 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12292 (parameters ⟨42,by decide⟩)
      (scalarRow12292.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12292 ⟨42,by decide⟩ ∧
    (scalarRow12292.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 ⟨42,by decide⟩ + (scalarRow12292.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12292.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12292.targetFrame := by
  norm_num [cap12292, scalarRow12292, sourceIndex, cell12292, BstLean.Part263.envelope, parameters]

theorem repair12292Cells (j : Fin 43) :
    0 ≤ cap12292 j ∧
    BstLean.Part263.envelope 12292 (parameters j) (scalarRow12292.table (sourceIndex j)).upper ≤ cap12292 j ∧
    (scalarRow12292.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12292 j + (scalarRow12292.table (sourceIndex j)).centre) /
      (scalarRow12292.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12292.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12292Cell0
  | ⟨1,_⟩ => exact repair12292Cell1
  | ⟨2,_⟩ => exact repair12292Cell2
  | ⟨3,_⟩ => exact repair12292Cell3
  | ⟨4,_⟩ => exact repair12292Cell4
  | ⟨5,_⟩ => exact repair12292Cell5
  | ⟨6,_⟩ => exact repair12292Cell6
  | ⟨7,_⟩ => exact repair12292Cell7
  | ⟨8,_⟩ => exact repair12292Cell8
  | ⟨9,_⟩ => exact repair12292Cell9
  | ⟨10,_⟩ => exact repair12292Cell10
  | ⟨11,_⟩ => exact repair12292Cell11
  | ⟨12,_⟩ => exact repair12292Cell12
  | ⟨13,_⟩ => exact repair12292Cell13
  | ⟨14,_⟩ => exact repair12292Cell14
  | ⟨15,_⟩ => exact repair12292Cell15
  | ⟨16,_⟩ => exact repair12292Cell16
  | ⟨17,_⟩ => exact repair12292Cell17
  | ⟨18,_⟩ => exact repair12292Cell18
  | ⟨19,_⟩ => exact repair12292Cell19
  | ⟨20,_⟩ => exact repair12292Cell20
  | ⟨21,_⟩ => exact repair12292Cell21
  | ⟨22,_⟩ => exact repair12292Cell22
  | ⟨23,_⟩ => exact repair12292Cell23
  | ⟨24,_⟩ => exact repair12292Cell24
  | ⟨25,_⟩ => exact repair12292Cell25
  | ⟨26,_⟩ => exact repair12292Cell26
  | ⟨27,_⟩ => exact repair12292Cell27
  | ⟨28,_⟩ => exact repair12292Cell28
  | ⟨29,_⟩ => exact repair12292Cell29
  | ⟨30,_⟩ => exact repair12292Cell30
  | ⟨31,_⟩ => exact repair12292Cell31
  | ⟨32,_⟩ => exact repair12292Cell32
  | ⟨33,_⟩ => exact repair12292Cell33
  | ⟨34,_⟩ => exact repair12292Cell34
  | ⟨35,_⟩ => exact repair12292Cell35
  | ⟨36,_⟩ => exact repair12292Cell36
  | ⟨37,_⟩ => exact repair12292Cell37
  | ⟨38,_⟩ => exact repair12292Cell38
  | ⟨39,_⟩ => exact repair12292Cell39
  | ⟨40,_⟩ => exact repair12292Cell40
  | ⟨41,_⟩ => exact repair12292Cell41
  | ⟨42,_⟩ => exact repair12292Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12292 : FrameRepair 12292 scalarRow12292 where
  cap := cap12292
  cap_nonneg := fun j => (repair12292Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12292])
  endpoint := fun j => (repair12292Cells j).2.1
  endpoint_upper := fun j => (repair12292Cells j).2.2.1
  frame := fun j => (repair12292Cells j).2.2.2

noncomputable def cap12293 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55189517 / 200000000 : ℝ)
  | ⟨1,_⟩ => (55270083 / 200000000 : ℝ)
  | ⟨2,_⟩ => (276752251 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277153089 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277552937 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (55590359 / 200000000 : ℝ)
  | ⟨6,_⟩ => (278349193 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (69686521 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279141999 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279536943 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (55986183 / 200000000 : ℝ)
  | ⟨11,_⟩ => (280323439 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (56143097 / 200000000 : ℝ)
  | ⟨13,_⟩ => (56221217 / 200000000 : ℝ)
  | ⟨14,_⟩ => (281496617 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (5637721 / 20000000 : ℝ)
  | ⟨16,_⟩ => (14113727 / 50000000 : ℝ)
  | ⟨17,_⟩ => (282662099 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141524359 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283434409 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283819173 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (14210151 / 50000000 : ℝ)
  | ⟨22,_⟩ => (35573243 / 125000000 : ℝ)
  | ⟨23,_⟩ => (8905233 / 31250000 : ℝ)
  | ⟨24,_⟩ => (71337139 / 250000000 : ℝ)
  | ⟨25,_⟩ => (35716037 / 125000000 : ℝ)
  | ⟨26,_⟩ => (28610763 / 100000000 : ℝ)
  | ⟨27,_⟩ => (57297113 / 200000000 : ℝ)
  | ⟨28,_⟩ => (71715651 / 250000000 : ℝ)
  | ⟨29,_⟩ => (287238747 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287613497 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143993931 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288361347 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288733441 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (14455233 / 50000000 : ℝ)
  | ⟨35,_⟩ => (289475007 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144922239 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290213089 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (72645209 / 250000000 : ℝ)
  | ⟨39,_⟩ => (29094721 / 100000000 : ℝ)
  | ⟨40,_⟩ => (11652509 / 40000000 : ℝ)
  | ⟨41,_⟩ => (72919347 / 250000000 : ℝ)
  | ⟨42,_⟩ => (730103 / 2500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12293Cell0 :
    0 ≤ cap12293 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨0,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12293 ⟨0,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨0,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell1 :
    0 ≤ cap12293 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨1,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12293 ⟨1,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨1,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell2 :
    0 ≤ cap12293 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨2,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12293 ⟨2,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨2,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell3 :
    0 ≤ cap12293 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨3,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12293 ⟨3,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨3,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell4 :
    0 ≤ cap12293 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨4,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12293 ⟨4,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨4,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell5 :
    0 ≤ cap12293 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨5,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12293 ⟨5,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨5,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell6 :
    0 ≤ cap12293 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨6,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12293 ⟨6,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨6,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell7 :
    0 ≤ cap12293 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨7,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12293 ⟨7,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨7,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell8 :
    0 ≤ cap12293 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨8,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12293 ⟨8,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨8,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell9 :
    0 ≤ cap12293 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨9,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12293 ⟨9,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨9,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell10 :
    0 ≤ cap12293 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨10,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12293 ⟨10,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨10,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell11 :
    0 ≤ cap12293 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨11,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12293 ⟨11,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨11,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell12 :
    0 ≤ cap12293 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨12,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12293 ⟨12,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨12,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell13 :
    0 ≤ cap12293 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨13,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12293 ⟨13,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨13,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell14 :
    0 ≤ cap12293 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨14,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12293 ⟨14,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨14,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell15 :
    0 ≤ cap12293 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨15,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12293 ⟨15,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨15,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell16 :
    0 ≤ cap12293 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨16,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12293 ⟨16,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨16,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell17 :
    0 ≤ cap12293 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨17,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12293 ⟨17,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨17,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell18 :
    0 ≤ cap12293 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨18,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12293 ⟨18,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨18,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell19 :
    0 ≤ cap12293 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨19,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12293 ⟨19,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨19,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell20 :
    0 ≤ cap12293 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨20,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12293 ⟨20,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨20,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell21 :
    0 ≤ cap12293 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨21,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12293 ⟨21,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨21,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell22 :
    0 ≤ cap12293 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨22,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12293 ⟨22,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨22,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell23 :
    0 ≤ cap12293 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨23,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12293 ⟨23,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨23,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell24 :
    0 ≤ cap12293 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨24,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12293 ⟨24,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨24,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell25 :
    0 ≤ cap12293 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨25,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12293 ⟨25,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨25,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell26 :
    0 ≤ cap12293 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨26,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12293 ⟨26,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨26,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell27 :
    0 ≤ cap12293 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨27,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12293 ⟨27,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨27,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell28 :
    0 ≤ cap12293 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨28,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12293 ⟨28,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨28,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell29 :
    0 ≤ cap12293 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨29,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12293 ⟨29,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨29,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell30 :
    0 ≤ cap12293 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨30,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12293 ⟨30,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨30,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell31 :
    0 ≤ cap12293 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨31,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12293 ⟨31,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨31,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell32 :
    0 ≤ cap12293 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨32,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12293 ⟨32,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨32,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell33 :
    0 ≤ cap12293 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨33,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12293 ⟨33,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨33,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell34 :
    0 ≤ cap12293 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨34,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12293 ⟨34,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨34,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell35 :
    0 ≤ cap12293 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨35,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12293 ⟨35,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨35,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell36 :
    0 ≤ cap12293 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨36,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12293 ⟨36,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨36,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell37 :
    0 ≤ cap12293 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨37,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12293 ⟨37,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨37,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell38 :
    0 ≤ cap12293 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨38,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12293 ⟨38,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨38,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell39 :
    0 ≤ cap12293 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨39,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12293 ⟨39,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨39,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell40 :
    0 ≤ cap12293 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨40,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12293 ⟨40,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨40,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell41 :
    0 ≤ cap12293 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨41,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12293 ⟨41,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨41,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cell42 :
    0 ≤ cap12293 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12293 (parameters ⟨42,by decide⟩)
      (scalarRow12293.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12293 ⟨42,by decide⟩ ∧
    (scalarRow12293.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 ⟨42,by decide⟩ + (scalarRow12293.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12293.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12293.targetFrame := by
  norm_num [cap12293, scalarRow12293, sourceIndex, cell12293, BstLean.Part263.envelope, parameters]

theorem repair12293Cells (j : Fin 43) :
    0 ≤ cap12293 j ∧
    BstLean.Part263.envelope 12293 (parameters j) (scalarRow12293.table (sourceIndex j)).upper ≤ cap12293 j ∧
    (scalarRow12293.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12293 j + (scalarRow12293.table (sourceIndex j)).centre) /
      (scalarRow12293.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12293.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12293Cell0
  | ⟨1,_⟩ => exact repair12293Cell1
  | ⟨2,_⟩ => exact repair12293Cell2
  | ⟨3,_⟩ => exact repair12293Cell3
  | ⟨4,_⟩ => exact repair12293Cell4
  | ⟨5,_⟩ => exact repair12293Cell5
  | ⟨6,_⟩ => exact repair12293Cell6
  | ⟨7,_⟩ => exact repair12293Cell7
  | ⟨8,_⟩ => exact repair12293Cell8
  | ⟨9,_⟩ => exact repair12293Cell9
  | ⟨10,_⟩ => exact repair12293Cell10
  | ⟨11,_⟩ => exact repair12293Cell11
  | ⟨12,_⟩ => exact repair12293Cell12
  | ⟨13,_⟩ => exact repair12293Cell13
  | ⟨14,_⟩ => exact repair12293Cell14
  | ⟨15,_⟩ => exact repair12293Cell15
  | ⟨16,_⟩ => exact repair12293Cell16
  | ⟨17,_⟩ => exact repair12293Cell17
  | ⟨18,_⟩ => exact repair12293Cell18
  | ⟨19,_⟩ => exact repair12293Cell19
  | ⟨20,_⟩ => exact repair12293Cell20
  | ⟨21,_⟩ => exact repair12293Cell21
  | ⟨22,_⟩ => exact repair12293Cell22
  | ⟨23,_⟩ => exact repair12293Cell23
  | ⟨24,_⟩ => exact repair12293Cell24
  | ⟨25,_⟩ => exact repair12293Cell25
  | ⟨26,_⟩ => exact repair12293Cell26
  | ⟨27,_⟩ => exact repair12293Cell27
  | ⟨28,_⟩ => exact repair12293Cell28
  | ⟨29,_⟩ => exact repair12293Cell29
  | ⟨30,_⟩ => exact repair12293Cell30
  | ⟨31,_⟩ => exact repair12293Cell31
  | ⟨32,_⟩ => exact repair12293Cell32
  | ⟨33,_⟩ => exact repair12293Cell33
  | ⟨34,_⟩ => exact repair12293Cell34
  | ⟨35,_⟩ => exact repair12293Cell35
  | ⟨36,_⟩ => exact repair12293Cell36
  | ⟨37,_⟩ => exact repair12293Cell37
  | ⟨38,_⟩ => exact repair12293Cell38
  | ⟨39,_⟩ => exact repair12293Cell39
  | ⟨40,_⟩ => exact repair12293Cell40
  | ⟨41,_⟩ => exact repair12293Cell41
  | ⟨42,_⟩ => exact repair12293Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12293 : FrameRepair 12293 scalarRow12293 where
  cap := cap12293
  cap_nonneg := fun j => (repair12293Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12293])
  endpoint := fun j => (repair12293Cells j).2.1
  endpoint_upper := fun j => (repair12293Cells j).2.2.1
  frame := fun j => (repair12293Cells j).2.2.2

noncomputable def cap12294 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275947509 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276350333 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138376081 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138576497 / 500000000 : ℝ)
  | ⟨4,_⟩ => (69388209 / 250000000 : ℝ)
  | ⟨5,_⟩ => (34743961 / 125000000 : ℝ)
  | ⟨6,_⟩ => (278349079 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (69686491 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279141873 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279536809 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (34991347 / 125000000 : ℝ)
  | ⟨11,_⟩ => (280323293 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280715333 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140552963 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281496453 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281885879 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282274363 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (56532383 / 200000000 : ℝ)
  | ⟨18,_⟩ => (17690533 / 62500000 : ℝ)
  | ⟨19,_⟩ => (283434213 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (28381897 / 100000000 : ℝ)
  | ⟨21,_⟩ => (71050703 / 250000000 : ℝ)
  | ⟨22,_⟩ => (284585729 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (71241809 / 250000000 : ℝ)
  | ⟨24,_⟩ => (285348329 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142864031 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286107391 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (7162133 / 25000000 : ℝ)
  | ⟨28,_⟩ => (286862353 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (28723849 / 100000000 : ℝ)
  | ⟨30,_⟩ => (287613233 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (35998449 / 125000000 : ℝ)
  | ⟨32,_⟩ => (288361071 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288733159 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72276093 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289474713 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144922089 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290212783 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (72645131 / 250000000 : ℝ)
  | ⟨39,_⟩ => (72736723 / 250000000 : ℝ)
  | ⟨40,_⟩ => (291312401 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145838529 / 500000000 : ℝ)
  | ⟨42,_⟩ => (9126277 / 31250000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12294Cell0 :
    0 ≤ cap12294 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨0,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12294 ⟨0,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨0,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell1 :
    0 ≤ cap12294 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨1,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12294 ⟨1,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨1,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell2 :
    0 ≤ cap12294 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨2,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12294 ⟨2,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨2,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell3 :
    0 ≤ cap12294 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨3,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12294 ⟨3,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨3,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell4 :
    0 ≤ cap12294 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨4,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12294 ⟨4,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨4,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell5 :
    0 ≤ cap12294 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨5,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12294 ⟨5,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨5,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell6 :
    0 ≤ cap12294 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨6,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12294 ⟨6,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨6,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell7 :
    0 ≤ cap12294 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨7,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12294 ⟨7,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨7,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell8 :
    0 ≤ cap12294 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨8,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12294 ⟨8,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨8,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell9 :
    0 ≤ cap12294 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨9,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12294 ⟨9,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨9,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell10 :
    0 ≤ cap12294 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨10,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12294 ⟨10,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨10,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell11 :
    0 ≤ cap12294 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨11,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12294 ⟨11,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨11,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell12 :
    0 ≤ cap12294 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨12,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12294 ⟨12,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨12,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell13 :
    0 ≤ cap12294 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨13,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12294 ⟨13,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨13,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell14 :
    0 ≤ cap12294 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨14,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12294 ⟨14,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨14,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell15 :
    0 ≤ cap12294 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨15,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12294 ⟨15,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨15,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell16 :
    0 ≤ cap12294 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨16,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12294 ⟨16,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨16,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell17 :
    0 ≤ cap12294 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨17,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12294 ⟨17,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨17,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell18 :
    0 ≤ cap12294 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨18,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12294 ⟨18,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨18,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell19 :
    0 ≤ cap12294 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨19,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12294 ⟨19,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨19,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell20 :
    0 ≤ cap12294 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨20,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12294 ⟨20,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨20,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell21 :
    0 ≤ cap12294 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨21,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12294 ⟨21,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨21,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell22 :
    0 ≤ cap12294 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨22,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12294 ⟨22,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨22,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell23 :
    0 ≤ cap12294 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨23,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12294 ⟨23,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨23,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell24 :
    0 ≤ cap12294 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨24,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12294 ⟨24,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨24,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell25 :
    0 ≤ cap12294 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨25,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12294 ⟨25,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨25,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell26 :
    0 ≤ cap12294 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨26,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12294 ⟨26,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨26,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell27 :
    0 ≤ cap12294 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨27,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12294 ⟨27,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨27,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell28 :
    0 ≤ cap12294 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨28,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12294 ⟨28,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨28,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell29 :
    0 ≤ cap12294 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨29,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12294 ⟨29,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨29,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell30 :
    0 ≤ cap12294 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨30,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12294 ⟨30,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨30,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell31 :
    0 ≤ cap12294 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨31,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12294 ⟨31,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨31,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell32 :
    0 ≤ cap12294 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨32,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12294 ⟨32,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨32,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell33 :
    0 ≤ cap12294 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨33,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12294 ⟨33,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨33,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell34 :
    0 ≤ cap12294 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨34,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12294 ⟨34,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨34,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell35 :
    0 ≤ cap12294 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨35,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12294 ⟨35,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨35,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell36 :
    0 ≤ cap12294 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨36,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12294 ⟨36,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨36,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell37 :
    0 ≤ cap12294 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨37,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12294 ⟨37,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨37,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell38 :
    0 ≤ cap12294 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨38,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12294 ⟨38,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨38,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell39 :
    0 ≤ cap12294 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨39,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12294 ⟨39,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨39,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell40 :
    0 ≤ cap12294 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨40,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12294 ⟨40,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨40,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell41 :
    0 ≤ cap12294 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨41,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12294 ⟨41,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨41,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cell42 :
    0 ≤ cap12294 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12294 (parameters ⟨42,by decide⟩)
      (scalarRow12294.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12294 ⟨42,by decide⟩ ∧
    (scalarRow12294.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 ⟨42,by decide⟩ + (scalarRow12294.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12294.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12294.targetFrame := by
  norm_num [cap12294, scalarRow12294, sourceIndex, cell12294, BstLean.Part263.envelope, parameters]

theorem repair12294Cells (j : Fin 43) :
    0 ≤ cap12294 j ∧
    BstLean.Part263.envelope 12294 (parameters j) (scalarRow12294.table (sourceIndex j)).upper ≤ cap12294 j ∧
    (scalarRow12294.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12294 j + (scalarRow12294.table (sourceIndex j)).centre) /
      (scalarRow12294.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12294.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12294Cell0
  | ⟨1,_⟩ => exact repair12294Cell1
  | ⟨2,_⟩ => exact repair12294Cell2
  | ⟨3,_⟩ => exact repair12294Cell3
  | ⟨4,_⟩ => exact repair12294Cell4
  | ⟨5,_⟩ => exact repair12294Cell5
  | ⟨6,_⟩ => exact repair12294Cell6
  | ⟨7,_⟩ => exact repair12294Cell7
  | ⟨8,_⟩ => exact repair12294Cell8
  | ⟨9,_⟩ => exact repair12294Cell9
  | ⟨10,_⟩ => exact repair12294Cell10
  | ⟨11,_⟩ => exact repair12294Cell11
  | ⟨12,_⟩ => exact repair12294Cell12
  | ⟨13,_⟩ => exact repair12294Cell13
  | ⟨14,_⟩ => exact repair12294Cell14
  | ⟨15,_⟩ => exact repair12294Cell15
  | ⟨16,_⟩ => exact repair12294Cell16
  | ⟨17,_⟩ => exact repair12294Cell17
  | ⟨18,_⟩ => exact repair12294Cell18
  | ⟨19,_⟩ => exact repair12294Cell19
  | ⟨20,_⟩ => exact repair12294Cell20
  | ⟨21,_⟩ => exact repair12294Cell21
  | ⟨22,_⟩ => exact repair12294Cell22
  | ⟨23,_⟩ => exact repair12294Cell23
  | ⟨24,_⟩ => exact repair12294Cell24
  | ⟨25,_⟩ => exact repair12294Cell25
  | ⟨26,_⟩ => exact repair12294Cell26
  | ⟨27,_⟩ => exact repair12294Cell27
  | ⟨28,_⟩ => exact repair12294Cell28
  | ⟨29,_⟩ => exact repair12294Cell29
  | ⟨30,_⟩ => exact repair12294Cell30
  | ⟨31,_⟩ => exact repair12294Cell31
  | ⟨32,_⟩ => exact repair12294Cell32
  | ⟨33,_⟩ => exact repair12294Cell33
  | ⟨34,_⟩ => exact repair12294Cell34
  | ⟨35,_⟩ => exact repair12294Cell35
  | ⟨36,_⟩ => exact repair12294Cell36
  | ⟨37,_⟩ => exact repair12294Cell37
  | ⟨38,_⟩ => exact repair12294Cell38
  | ⟨39,_⟩ => exact repair12294Cell39
  | ⟨40,_⟩ => exact repair12294Cell40
  | ⟨41,_⟩ => exact repair12294Cell41
  | ⟨42,_⟩ => exact repair12294Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12294 : FrameRepair 12294 scalarRow12294 where
  cap := cap12294
  cap_nonneg := fun j => (repair12294Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12294])
  endpoint := fun j => (repair12294Cells j).2.1
  endpoint_upper := fun j => (repair12294Cells j).2.2.1
  frame := fun j => (repair12294Cells j).2.2.2

noncomputable def cap12295 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137973717 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276350251 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138376037 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277152899 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (55510547 / 200000000 : ℝ)
  | ⟨5,_⟩ => (13897579 / 50000000 : ℝ)
  | ⟨6,_⟩ => (55669793 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278745843 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139570873 / 500000000 : ℝ)
  | ⟨9,_⟩ => (69884169 / 250000000 : ℝ)
  | ⟨10,_⟩ => (69982659 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280323147 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280715181 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (35138221 / 125000000 : ℝ)
  | ⟨14,_⟩ => (8796759 / 31250000 : ℝ)
  | ⟨15,_⟩ => (70471427 / 250000000 : ℝ)
  | ⟨16,_⟩ => (56454837 / 200000000 : ℝ)
  | ⟨17,_⟩ => (282661731 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141524169 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283434017 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (17738673 / 62500000 : ℝ)
  | ⟨21,_⟩ => (284202603 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142292757 / 500000000 : ℝ)
  | ⟨23,_⟩ => (56993403 / 200000000 : ℝ)
  | ⟨24,_⟩ => (285348103 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285727829 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (17881697 / 62500000 : ℝ)
  | ⟨27,_⟩ => (11459403 / 40000000 : ℝ)
  | ⟨28,_⟩ => (286862101 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (35904779 / 125000000 : ℝ)
  | ⟨30,_⟩ => (287612969 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287987323 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (57672159 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288732877 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72276021 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289474419 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144921939 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145106239 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72645053 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145473287 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291312077 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291676729 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (18252533 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12295Cell0 :
    0 ≤ cap12295 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨0,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12295 ⟨0,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨0,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell1 :
    0 ≤ cap12295 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨1,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12295 ⟨1,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨1,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell2 :
    0 ≤ cap12295 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨2,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12295 ⟨2,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨2,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell3 :
    0 ≤ cap12295 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨3,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12295 ⟨3,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨3,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell4 :
    0 ≤ cap12295 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨4,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12295 ⟨4,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨4,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell5 :
    0 ≤ cap12295 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨5,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12295 ⟨5,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨5,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell6 :
    0 ≤ cap12295 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨6,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12295 ⟨6,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨6,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell7 :
    0 ≤ cap12295 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨7,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12295 ⟨7,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨7,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell8 :
    0 ≤ cap12295 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨8,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12295 ⟨8,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨8,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell9 :
    0 ≤ cap12295 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨9,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12295 ⟨9,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨9,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell10 :
    0 ≤ cap12295 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨10,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12295 ⟨10,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨10,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell11 :
    0 ≤ cap12295 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨11,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12295 ⟨11,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨11,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell12 :
    0 ≤ cap12295 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨12,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12295 ⟨12,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨12,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell13 :
    0 ≤ cap12295 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨13,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12295 ⟨13,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨13,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell14 :
    0 ≤ cap12295 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨14,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12295 ⟨14,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨14,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell15 :
    0 ≤ cap12295 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨15,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12295 ⟨15,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨15,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell16 :
    0 ≤ cap12295 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨16,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12295 ⟨16,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨16,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell17 :
    0 ≤ cap12295 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨17,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12295 ⟨17,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨17,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell18 :
    0 ≤ cap12295 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨18,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12295 ⟨18,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨18,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell19 :
    0 ≤ cap12295 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨19,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12295 ⟨19,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨19,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell20 :
    0 ≤ cap12295 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨20,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12295 ⟨20,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨20,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell21 :
    0 ≤ cap12295 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨21,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12295 ⟨21,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨21,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell22 :
    0 ≤ cap12295 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨22,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12295 ⟨22,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨22,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell23 :
    0 ≤ cap12295 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨23,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12295 ⟨23,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨23,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell24 :
    0 ≤ cap12295 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨24,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12295 ⟨24,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨24,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell25 :
    0 ≤ cap12295 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨25,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12295 ⟨25,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨25,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell26 :
    0 ≤ cap12295 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨26,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12295 ⟨26,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨26,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell27 :
    0 ≤ cap12295 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨27,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12295 ⟨27,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨27,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell28 :
    0 ≤ cap12295 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨28,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12295 ⟨28,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨28,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell29 :
    0 ≤ cap12295 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨29,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12295 ⟨29,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨29,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell30 :
    0 ≤ cap12295 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨30,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12295 ⟨30,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨30,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell31 :
    0 ≤ cap12295 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨31,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12295 ⟨31,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨31,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell32 :
    0 ≤ cap12295 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨32,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12295 ⟨32,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨32,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell33 :
    0 ≤ cap12295 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨33,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12295 ⟨33,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨33,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell34 :
    0 ≤ cap12295 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨34,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12295 ⟨34,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨34,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell35 :
    0 ≤ cap12295 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨35,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12295 ⟨35,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨35,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell36 :
    0 ≤ cap12295 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨36,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12295 ⟨36,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨36,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell37 :
    0 ≤ cap12295 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨37,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12295 ⟨37,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨37,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell38 :
    0 ≤ cap12295 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨38,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12295 ⟨38,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨38,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell39 :
    0 ≤ cap12295 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨39,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12295 ⟨39,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨39,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell40 :
    0 ≤ cap12295 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨40,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12295 ⟨40,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨40,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell41 :
    0 ≤ cap12295 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨41,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12295 ⟨41,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨41,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cell42 :
    0 ≤ cap12295 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12295 (parameters ⟨42,by decide⟩)
      (scalarRow12295.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12295 ⟨42,by decide⟩ ∧
    (scalarRow12295.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 ⟨42,by decide⟩ + (scalarRow12295.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12295.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12295.targetFrame := by
  norm_num [cap12295, scalarRow12295, sourceIndex, cell12295, BstLean.Part263.envelope, parameters]

theorem repair12295Cells (j : Fin 43) :
    0 ≤ cap12295 j ∧
    BstLean.Part263.envelope 12295 (parameters j) (scalarRow12295.table (sourceIndex j)).upper ≤ cap12295 j ∧
    (scalarRow12295.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12295 j + (scalarRow12295.table (sourceIndex j)).centre) /
      (scalarRow12295.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12295.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12295Cell0
  | ⟨1,_⟩ => exact repair12295Cell1
  | ⟨2,_⟩ => exact repair12295Cell2
  | ⟨3,_⟩ => exact repair12295Cell3
  | ⟨4,_⟩ => exact repair12295Cell4
  | ⟨5,_⟩ => exact repair12295Cell5
  | ⟨6,_⟩ => exact repair12295Cell6
  | ⟨7,_⟩ => exact repair12295Cell7
  | ⟨8,_⟩ => exact repair12295Cell8
  | ⟨9,_⟩ => exact repair12295Cell9
  | ⟨10,_⟩ => exact repair12295Cell10
  | ⟨11,_⟩ => exact repair12295Cell11
  | ⟨12,_⟩ => exact repair12295Cell12
  | ⟨13,_⟩ => exact repair12295Cell13
  | ⟨14,_⟩ => exact repair12295Cell14
  | ⟨15,_⟩ => exact repair12295Cell15
  | ⟨16,_⟩ => exact repair12295Cell16
  | ⟨17,_⟩ => exact repair12295Cell17
  | ⟨18,_⟩ => exact repair12295Cell18
  | ⟨19,_⟩ => exact repair12295Cell19
  | ⟨20,_⟩ => exact repair12295Cell20
  | ⟨21,_⟩ => exact repair12295Cell21
  | ⟨22,_⟩ => exact repair12295Cell22
  | ⟨23,_⟩ => exact repair12295Cell23
  | ⟨24,_⟩ => exact repair12295Cell24
  | ⟨25,_⟩ => exact repair12295Cell25
  | ⟨26,_⟩ => exact repair12295Cell26
  | ⟨27,_⟩ => exact repair12295Cell27
  | ⟨28,_⟩ => exact repair12295Cell28
  | ⟨29,_⟩ => exact repair12295Cell29
  | ⟨30,_⟩ => exact repair12295Cell30
  | ⟨31,_⟩ => exact repair12295Cell31
  | ⟨32,_⟩ => exact repair12295Cell32
  | ⟨33,_⟩ => exact repair12295Cell33
  | ⟨34,_⟩ => exact repair12295Cell34
  | ⟨35,_⟩ => exact repair12295Cell35
  | ⟨36,_⟩ => exact repair12295Cell36
  | ⟨37,_⟩ => exact repair12295Cell37
  | ⟨38,_⟩ => exact repair12295Cell38
  | ⟨39,_⟩ => exact repair12295Cell39
  | ⟨40,_⟩ => exact repair12295Cell40
  | ⟨41,_⟩ => exact repair12295Cell41
  | ⟨42,_⟩ => exact repair12295Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12295 : FrameRepair 12295 scalarRow12295 where
  cap := cap12295
  cap_nonneg := fun j => (repair12295Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12295])
  endpoint := fun j => (repair12295Cells j).2.1
  endpoint_upper := fun j => (repair12295Cells j).2.2.1
  frame := fun j => (repair12295Cells j).2.2.2

noncomputable def cap12296 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275947359 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276350169 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138375993 / 500000000 : ℝ)
  | ⟨3,_⟩ => (55430561 / 200000000 : ℝ)
  | ⟨4,_⟩ => (277552633 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (17371967 / 62500000 : ℝ)
  | ⟨6,_⟩ => (278348851 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278745723 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279141619 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279536543 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279930497 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140161501 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280715029 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (28110561 / 100000000 : ℝ)
  | ⟨14,_⟩ => (281496123 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281885537 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (35284251 / 125000000 : ℝ)
  | ⟨17,_⟩ => (70665387 / 250000000 : ℝ)
  | ⟨18,_⟩ => (283048149 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283433821 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141909283 / 500000000 : ℝ)
  | ⟨21,_⟩ => (56840479 / 200000000 : ℝ)
  | ⟨22,_⟩ => (2845853 / 10000000 : ℝ)
  | ⟨23,_⟩ => (142483397 / 500000000 : ℝ)
  | ⟨24,_⟩ => (71336969 / 250000000 : ℝ)
  | ⟨25,_⟩ => (71431899 / 250000000 : ℝ)
  | ⟨26,_⟩ => (8940841 / 31250000 : ℝ)
  | ⟨27,_⟩ => (286484829 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (5737237 / 20000000 : ℝ)
  | ⟨29,_⟩ => (143618987 / 500000000 : ℝ)
  | ⟨30,_⟩ => (143806353 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287987053 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288360519 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (57746519 / 200000000 : ℝ)
  | ⟨34,_⟩ => (72275949 / 250000000 : ℝ)
  | ⟨35,_⟩ => (2315793 / 8000000 : ℝ)
  | ⟨36,_⟩ => (144921789 / 500000000 : ℝ)
  | ⟨37,_⟩ => (72553043 / 250000000 : ℝ)
  | ⟨38,_⟩ => (2905799 / 10000000 : ℝ)
  | ⟨39,_⟩ => (18184141 / 62500000 : ℝ)
  | ⟨40,_⟩ => (291311753 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291676399 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292040193 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12296Cell0 :
    0 ≤ cap12296 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨0,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12296 ⟨0,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨0,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell1 :
    0 ≤ cap12296 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨1,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12296 ⟨1,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨1,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell2 :
    0 ≤ cap12296 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨2,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12296 ⟨2,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨2,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell3 :
    0 ≤ cap12296 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨3,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12296 ⟨3,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨3,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell4 :
    0 ≤ cap12296 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨4,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12296 ⟨4,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨4,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell5 :
    0 ≤ cap12296 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨5,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12296 ⟨5,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨5,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell6 :
    0 ≤ cap12296 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨6,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12296 ⟨6,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨6,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell7 :
    0 ≤ cap12296 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨7,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12296 ⟨7,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨7,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell8 :
    0 ≤ cap12296 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨8,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12296 ⟨8,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨8,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell9 :
    0 ≤ cap12296 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨9,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12296 ⟨9,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨9,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell10 :
    0 ≤ cap12296 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨10,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12296 ⟨10,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨10,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell11 :
    0 ≤ cap12296 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨11,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12296 ⟨11,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨11,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell12 :
    0 ≤ cap12296 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨12,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12296 ⟨12,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨12,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell13 :
    0 ≤ cap12296 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨13,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12296 ⟨13,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨13,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell14 :
    0 ≤ cap12296 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨14,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12296 ⟨14,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨14,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell15 :
    0 ≤ cap12296 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨15,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12296 ⟨15,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨15,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell16 :
    0 ≤ cap12296 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨16,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12296 ⟨16,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨16,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell17 :
    0 ≤ cap12296 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨17,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12296 ⟨17,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨17,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell18 :
    0 ≤ cap12296 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨18,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12296 ⟨18,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨18,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell19 :
    0 ≤ cap12296 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨19,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12296 ⟨19,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨19,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell20 :
    0 ≤ cap12296 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨20,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12296 ⟨20,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨20,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell21 :
    0 ≤ cap12296 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨21,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12296 ⟨21,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨21,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell22 :
    0 ≤ cap12296 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨22,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12296 ⟨22,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨22,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell23 :
    0 ≤ cap12296 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨23,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12296 ⟨23,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨23,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell24 :
    0 ≤ cap12296 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨24,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12296 ⟨24,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨24,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell25 :
    0 ≤ cap12296 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨25,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12296 ⟨25,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨25,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell26 :
    0 ≤ cap12296 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨26,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12296 ⟨26,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨26,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell27 :
    0 ≤ cap12296 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨27,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12296 ⟨27,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨27,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell28 :
    0 ≤ cap12296 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨28,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12296 ⟨28,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨28,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell29 :
    0 ≤ cap12296 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨29,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12296 ⟨29,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨29,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell30 :
    0 ≤ cap12296 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨30,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12296 ⟨30,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨30,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell31 :
    0 ≤ cap12296 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨31,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12296 ⟨31,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨31,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell32 :
    0 ≤ cap12296 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨32,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12296 ⟨32,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨32,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell33 :
    0 ≤ cap12296 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨33,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12296 ⟨33,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨33,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell34 :
    0 ≤ cap12296 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨34,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12296 ⟨34,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨34,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell35 :
    0 ≤ cap12296 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨35,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12296 ⟨35,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨35,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell36 :
    0 ≤ cap12296 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨36,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12296 ⟨36,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨36,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell37 :
    0 ≤ cap12296 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨37,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12296 ⟨37,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨37,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell38 :
    0 ≤ cap12296 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨38,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12296 ⟨38,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨38,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell39 :
    0 ≤ cap12296 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨39,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12296 ⟨39,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨39,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell40 :
    0 ≤ cap12296 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨40,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12296 ⟨40,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨40,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell41 :
    0 ≤ cap12296 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨41,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12296 ⟨41,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨41,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cell42 :
    0 ≤ cap12296 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12296 (parameters ⟨42,by decide⟩)
      (scalarRow12296.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12296 ⟨42,by decide⟩ ∧
    (scalarRow12296.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 ⟨42,by decide⟩ + (scalarRow12296.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12296.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12296.targetFrame := by
  norm_num [cap12296, scalarRow12296, sourceIndex, cell12296, BstLean.Part263.envelope, parameters]

theorem repair12296Cells (j : Fin 43) :
    0 ≤ cap12296 j ∧
    BstLean.Part263.envelope 12296 (parameters j) (scalarRow12296.table (sourceIndex j)).upper ≤ cap12296 j ∧
    (scalarRow12296.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12296 j + (scalarRow12296.table (sourceIndex j)).centre) /
      (scalarRow12296.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12296.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12296Cell0
  | ⟨1,_⟩ => exact repair12296Cell1
  | ⟨2,_⟩ => exact repair12296Cell2
  | ⟨3,_⟩ => exact repair12296Cell3
  | ⟨4,_⟩ => exact repair12296Cell4
  | ⟨5,_⟩ => exact repair12296Cell5
  | ⟨6,_⟩ => exact repair12296Cell6
  | ⟨7,_⟩ => exact repair12296Cell7
  | ⟨8,_⟩ => exact repair12296Cell8
  | ⟨9,_⟩ => exact repair12296Cell9
  | ⟨10,_⟩ => exact repair12296Cell10
  | ⟨11,_⟩ => exact repair12296Cell11
  | ⟨12,_⟩ => exact repair12296Cell12
  | ⟨13,_⟩ => exact repair12296Cell13
  | ⟨14,_⟩ => exact repair12296Cell14
  | ⟨15,_⟩ => exact repair12296Cell15
  | ⟨16,_⟩ => exact repair12296Cell16
  | ⟨17,_⟩ => exact repair12296Cell17
  | ⟨18,_⟩ => exact repair12296Cell18
  | ⟨19,_⟩ => exact repair12296Cell19
  | ⟨20,_⟩ => exact repair12296Cell20
  | ⟨21,_⟩ => exact repair12296Cell21
  | ⟨22,_⟩ => exact repair12296Cell22
  | ⟨23,_⟩ => exact repair12296Cell23
  | ⟨24,_⟩ => exact repair12296Cell24
  | ⟨25,_⟩ => exact repair12296Cell25
  | ⟨26,_⟩ => exact repair12296Cell26
  | ⟨27,_⟩ => exact repair12296Cell27
  | ⟨28,_⟩ => exact repair12296Cell28
  | ⟨29,_⟩ => exact repair12296Cell29
  | ⟨30,_⟩ => exact repair12296Cell30
  | ⟨31,_⟩ => exact repair12296Cell31
  | ⟨32,_⟩ => exact repair12296Cell32
  | ⟨33,_⟩ => exact repair12296Cell33
  | ⟨34,_⟩ => exact repair12296Cell34
  | ⟨35,_⟩ => exact repair12296Cell35
  | ⟨36,_⟩ => exact repair12296Cell36
  | ⟨37,_⟩ => exact repair12296Cell37
  | ⟨38,_⟩ => exact repair12296Cell38
  | ⟨39,_⟩ => exact repair12296Cell39
  | ⟨40,_⟩ => exact repair12296Cell40
  | ⟨41,_⟩ => exact repair12296Cell41
  | ⟨42,_⟩ => exact repair12296Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12296 : FrameRepair 12296 scalarRow12296 where
  cap := cap12296
  cap_nonneg := fun j => (repair12296Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12296])
  endpoint := fun j => (repair12296Cells j).2.1
  endpoint_upper := fun j => (repair12296Cells j).2.2.1
  frame := fun j => (repair12296Cells j).2.2.2

noncomputable def cap12297 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275947283 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276350087 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276751897 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (27715271 / 100000000 : ℝ)
  | ⟨4,_⟩ => (69388133 / 250000000 : ℝ)
  | ⟨5,_⟩ => (55590273 / 200000000 : ℝ)
  | ⟨6,_⟩ => (278348737 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139372801 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69785373 / 250000000 : ℝ)
  | ⟨9,_⟩ => (27953641 / 100000000 : ℝ)
  | ⟨10,_⟩ => (279930357 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (35040357 / 125000000 : ℝ)
  | ⟨12,_⟩ => (280714877 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281105451 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140747979 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140942683 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282273831 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (70665341 / 250000000 : ℝ)
  | ⟨18,_⟩ => (283047959 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (2267469 / 8000000 : ℝ)
  | ⟨20,_⟩ => (70954591 / 250000000 : ℝ)
  | ⟨21,_⟩ => (142101093 / 500000000 : ℝ)
  | ⟨22,_⟩ => (56917017 / 200000000 : ℝ)
  | ⟨23,_⟩ => (284966573 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285347649 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285727363 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286106673 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (35810573 / 125000000 : ℝ)
  | ⟨28,_⟩ => (143430799 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287237717 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143806221 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287986783 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288360243 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288732313 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72275877 / 250000000 : ℝ)
  | ⟨35,_⟩ => (36184229 / 125000000 : ℝ)
  | ⟨36,_⟩ => (144921639 / 500000000 : ℝ)
  | ⟨37,_⟩ => (145105933 / 500000000 : ℝ)
  | ⟨38,_⟩ => (72644897 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145472969 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291311429 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291676069 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292039857 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12297Cell0 :
    0 ≤ cap12297 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨0,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12297 ⟨0,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨0,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell1 :
    0 ≤ cap12297 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨1,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12297 ⟨1,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨1,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell2 :
    0 ≤ cap12297 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨2,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12297 ⟨2,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨2,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell3 :
    0 ≤ cap12297 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨3,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12297 ⟨3,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨3,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell4 :
    0 ≤ cap12297 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨4,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12297 ⟨4,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨4,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell5 :
    0 ≤ cap12297 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨5,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12297 ⟨5,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨5,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell6 :
    0 ≤ cap12297 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨6,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12297 ⟨6,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨6,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell7 :
    0 ≤ cap12297 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨7,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12297 ⟨7,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨7,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell8 :
    0 ≤ cap12297 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨8,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12297 ⟨8,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨8,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell9 :
    0 ≤ cap12297 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨9,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12297 ⟨9,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨9,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell10 :
    0 ≤ cap12297 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨10,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12297 ⟨10,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨10,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell11 :
    0 ≤ cap12297 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨11,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12297 ⟨11,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨11,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell12 :
    0 ≤ cap12297 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨12,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12297 ⟨12,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨12,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell13 :
    0 ≤ cap12297 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨13,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12297 ⟨13,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨13,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell14 :
    0 ≤ cap12297 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨14,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12297 ⟨14,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨14,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell15 :
    0 ≤ cap12297 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨15,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12297 ⟨15,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨15,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell16 :
    0 ≤ cap12297 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨16,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12297 ⟨16,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨16,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell17 :
    0 ≤ cap12297 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨17,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12297 ⟨17,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨17,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell18 :
    0 ≤ cap12297 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨18,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12297 ⟨18,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨18,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell19 :
    0 ≤ cap12297 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨19,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12297 ⟨19,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨19,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell20 :
    0 ≤ cap12297 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨20,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12297 ⟨20,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨20,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell21 :
    0 ≤ cap12297 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨21,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12297 ⟨21,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨21,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell22 :
    0 ≤ cap12297 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨22,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12297 ⟨22,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨22,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell23 :
    0 ≤ cap12297 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨23,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12297 ⟨23,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨23,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell24 :
    0 ≤ cap12297 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨24,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12297 ⟨24,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨24,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell25 :
    0 ≤ cap12297 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨25,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12297 ⟨25,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨25,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell26 :
    0 ≤ cap12297 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨26,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12297 ⟨26,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨26,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell27 :
    0 ≤ cap12297 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨27,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12297 ⟨27,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨27,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell28 :
    0 ≤ cap12297 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨28,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12297 ⟨28,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨28,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell29 :
    0 ≤ cap12297 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨29,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12297 ⟨29,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨29,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell30 :
    0 ≤ cap12297 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨30,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12297 ⟨30,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨30,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell31 :
    0 ≤ cap12297 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨31,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12297 ⟨31,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨31,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell32 :
    0 ≤ cap12297 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨32,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12297 ⟨32,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨32,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell33 :
    0 ≤ cap12297 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨33,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12297 ⟨33,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨33,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell34 :
    0 ≤ cap12297 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨34,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12297 ⟨34,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨34,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell35 :
    0 ≤ cap12297 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨35,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12297 ⟨35,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨35,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell36 :
    0 ≤ cap12297 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨36,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12297 ⟨36,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨36,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell37 :
    0 ≤ cap12297 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨37,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12297 ⟨37,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨37,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell38 :
    0 ≤ cap12297 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨38,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12297 ⟨38,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨38,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell39 :
    0 ≤ cap12297 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨39,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12297 ⟨39,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨39,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell40 :
    0 ≤ cap12297 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨40,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12297 ⟨40,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨40,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell41 :
    0 ≤ cap12297 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨41,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12297 ⟨41,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨41,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cell42 :
    0 ≤ cap12297 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12297 (parameters ⟨42,by decide⟩)
      (scalarRow12297.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12297 ⟨42,by decide⟩ ∧
    (scalarRow12297.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 ⟨42,by decide⟩ + (scalarRow12297.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12297.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12297.targetFrame := by
  norm_num [cap12297, scalarRow12297, sourceIndex, cell12297, BstLean.Part263.envelope, parameters]

theorem repair12297Cells (j : Fin 43) :
    0 ≤ cap12297 j ∧
    BstLean.Part263.envelope 12297 (parameters j) (scalarRow12297.table (sourceIndex j)).upper ≤ cap12297 j ∧
    (scalarRow12297.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12297 j + (scalarRow12297.table (sourceIndex j)).centre) /
      (scalarRow12297.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12297.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12297Cell0
  | ⟨1,_⟩ => exact repair12297Cell1
  | ⟨2,_⟩ => exact repair12297Cell2
  | ⟨3,_⟩ => exact repair12297Cell3
  | ⟨4,_⟩ => exact repair12297Cell4
  | ⟨5,_⟩ => exact repair12297Cell5
  | ⟨6,_⟩ => exact repair12297Cell6
  | ⟨7,_⟩ => exact repair12297Cell7
  | ⟨8,_⟩ => exact repair12297Cell8
  | ⟨9,_⟩ => exact repair12297Cell9
  | ⟨10,_⟩ => exact repair12297Cell10
  | ⟨11,_⟩ => exact repair12297Cell11
  | ⟨12,_⟩ => exact repair12297Cell12
  | ⟨13,_⟩ => exact repair12297Cell13
  | ⟨14,_⟩ => exact repair12297Cell14
  | ⟨15,_⟩ => exact repair12297Cell15
  | ⟨16,_⟩ => exact repair12297Cell16
  | ⟨17,_⟩ => exact repair12297Cell17
  | ⟨18,_⟩ => exact repair12297Cell18
  | ⟨19,_⟩ => exact repair12297Cell19
  | ⟨20,_⟩ => exact repair12297Cell20
  | ⟨21,_⟩ => exact repair12297Cell21
  | ⟨22,_⟩ => exact repair12297Cell22
  | ⟨23,_⟩ => exact repair12297Cell23
  | ⟨24,_⟩ => exact repair12297Cell24
  | ⟨25,_⟩ => exact repair12297Cell25
  | ⟨26,_⟩ => exact repair12297Cell26
  | ⟨27,_⟩ => exact repair12297Cell27
  | ⟨28,_⟩ => exact repair12297Cell28
  | ⟨29,_⟩ => exact repair12297Cell29
  | ⟨30,_⟩ => exact repair12297Cell30
  | ⟨31,_⟩ => exact repair12297Cell31
  | ⟨32,_⟩ => exact repair12297Cell32
  | ⟨33,_⟩ => exact repair12297Cell33
  | ⟨34,_⟩ => exact repair12297Cell34
  | ⟨35,_⟩ => exact repair12297Cell35
  | ⟨36,_⟩ => exact repair12297Cell36
  | ⟨37,_⟩ => exact repair12297Cell37
  | ⟨38,_⟩ => exact repair12297Cell38
  | ⟨39,_⟩ => exact repair12297Cell39
  | ⟨40,_⟩ => exact repair12297Cell40
  | ⟨41,_⟩ => exact repair12297Cell41
  | ⟨42,_⟩ => exact repair12297Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12297 : FrameRepair 12297 scalarRow12297 where
  cap := cap12297
  cap_nonneg := fun j => (repair12297Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12297])
  endpoint := fun j => (repair12297Cells j).2.1
  endpoint_upper := fun j => (repair12297Cells j).2.2.1
  frame := fun j => (repair12297Cells j).2.2.2

noncomputable def cap12298 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34493401 / 125000000 : ℝ)
  | ⟨1,_⟩ => (138175003 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276751809 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (55430523 / 200000000 : ℝ)
  | ⟨4,_⟩ => (277552431 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277951257 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278348623 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139372741 / 500000000 : ℝ)
  | ⟨8,_⟩ => (139570683 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279536277 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (139965109 / 500000000 : ℝ)
  | ⟨11,_⟩ => (28032271 / 100000000 : ℝ)
  | ⟨12,_⟩ => (11228589 / 40000000 : ℝ)
  | ⟨13,_⟩ => (281105293 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140747897 / 500000000 : ℝ)
  | ⟨15,_⟩ => (56377039 / 200000000 : ℝ)
  | ⟨16,_⟩ => (141136827 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282661181 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283047769 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283433429 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141909081 / 500000000 : ℝ)
  | ⟨21,_⟩ => (142100989 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284584871 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (17810397 / 62500000 : ℝ)
  | ⟨24,_⟩ => (142673711 / 500000000 : ℝ)
  | ⟨25,_⟩ => (28572713 / 100000000 : ℝ)
  | ⟨26,_⟩ => (143053217 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286484339 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286861347 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287237459 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287612179 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287986513 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (9011249 / 31250000 : ℝ)
  | ⟨33,_⟩ => (2255719 / 7812500 : ℝ)
  | ⟨34,_⟩ => (14455161 / 50000000 : ℝ)
  | ⟨35,_⟩ => (144736769 / 500000000 : ℝ)
  | ⟨36,_⟩ => (144921489 / 500000000 : ℝ)
  | ⟨37,_⟩ => (7255289 / 25000000 : ℝ)
  | ⟨38,_⟩ => (72644819 / 250000000 : ℝ)
  | ⟨39,_⟩ => (14547281 / 50000000 : ℝ)
  | ⟨40,_⟩ => (145655553 / 500000000 : ℝ)
  | ⟨41,_⟩ => (14583787 / 50000000 : ℝ)
  | ⟨42,_⟩ => (146019761 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12298Cell0 :
    0 ≤ cap12298 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨0,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12298 ⟨0,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨0,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell1 :
    0 ≤ cap12298 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨1,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12298 ⟨1,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨1,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell2 :
    0 ≤ cap12298 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨2,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12298 ⟨2,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨2,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell3 :
    0 ≤ cap12298 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨3,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12298 ⟨3,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨3,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell4 :
    0 ≤ cap12298 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨4,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12298 ⟨4,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨4,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell5 :
    0 ≤ cap12298 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨5,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12298 ⟨5,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨5,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell6 :
    0 ≤ cap12298 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨6,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12298 ⟨6,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨6,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell7 :
    0 ≤ cap12298 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨7,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12298 ⟨7,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨7,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell8 :
    0 ≤ cap12298 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨8,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12298 ⟨8,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨8,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell9 :
    0 ≤ cap12298 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨9,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12298 ⟨9,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨9,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell10 :
    0 ≤ cap12298 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨10,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12298 ⟨10,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨10,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell11 :
    0 ≤ cap12298 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨11,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12298 ⟨11,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨11,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell12 :
    0 ≤ cap12298 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨12,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12298 ⟨12,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨12,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell13 :
    0 ≤ cap12298 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨13,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12298 ⟨13,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨13,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell14 :
    0 ≤ cap12298 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨14,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12298 ⟨14,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨14,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell15 :
    0 ≤ cap12298 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨15,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12298 ⟨15,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨15,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell16 :
    0 ≤ cap12298 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨16,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12298 ⟨16,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨16,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell17 :
    0 ≤ cap12298 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨17,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12298 ⟨17,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨17,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell18 :
    0 ≤ cap12298 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨18,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12298 ⟨18,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨18,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell19 :
    0 ≤ cap12298 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨19,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12298 ⟨19,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨19,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell20 :
    0 ≤ cap12298 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨20,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12298 ⟨20,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨20,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell21 :
    0 ≤ cap12298 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨21,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12298 ⟨21,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨21,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell22 :
    0 ≤ cap12298 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨22,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12298 ⟨22,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨22,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell23 :
    0 ≤ cap12298 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨23,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12298 ⟨23,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨23,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell24 :
    0 ≤ cap12298 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨24,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12298 ⟨24,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨24,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell25 :
    0 ≤ cap12298 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨25,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12298 ⟨25,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨25,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell26 :
    0 ≤ cap12298 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨26,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12298 ⟨26,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨26,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell27 :
    0 ≤ cap12298 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨27,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12298 ⟨27,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨27,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell28 :
    0 ≤ cap12298 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨28,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12298 ⟨28,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨28,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell29 :
    0 ≤ cap12298 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨29,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12298 ⟨29,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨29,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell30 :
    0 ≤ cap12298 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨30,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12298 ⟨30,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨30,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell31 :
    0 ≤ cap12298 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨31,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12298 ⟨31,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨31,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell32 :
    0 ≤ cap12298 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨32,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12298 ⟨32,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨32,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell33 :
    0 ≤ cap12298 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨33,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12298 ⟨33,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨33,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell34 :
    0 ≤ cap12298 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨34,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12298 ⟨34,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨34,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell35 :
    0 ≤ cap12298 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨35,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12298 ⟨35,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨35,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell36 :
    0 ≤ cap12298 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨36,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12298 ⟨36,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨36,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell37 :
    0 ≤ cap12298 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨37,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12298 ⟨37,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨37,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell38 :
    0 ≤ cap12298 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨38,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12298 ⟨38,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨38,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell39 :
    0 ≤ cap12298 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨39,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12298 ⟨39,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨39,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell40 :
    0 ≤ cap12298 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨40,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12298 ⟨40,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨40,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell41 :
    0 ≤ cap12298 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨41,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12298 ⟨41,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨41,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cell42 :
    0 ≤ cap12298 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12298 (parameters ⟨42,by decide⟩)
      (scalarRow12298.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12298 ⟨42,by decide⟩ ∧
    (scalarRow12298.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 ⟨42,by decide⟩ + (scalarRow12298.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12298.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12298.targetFrame := by
  norm_num [cap12298, scalarRow12298, sourceIndex, cell12298, BstLean.Part263.envelope, parameters]

theorem repair12298Cells (j : Fin 43) :
    0 ≤ cap12298 j ∧
    BstLean.Part263.envelope 12298 (parameters j) (scalarRow12298.table (sourceIndex j)).upper ≤ cap12298 j ∧
    (scalarRow12298.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12298 j + (scalarRow12298.table (sourceIndex j)).centre) /
      (scalarRow12298.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12298.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12298Cell0
  | ⟨1,_⟩ => exact repair12298Cell1
  | ⟨2,_⟩ => exact repair12298Cell2
  | ⟨3,_⟩ => exact repair12298Cell3
  | ⟨4,_⟩ => exact repair12298Cell4
  | ⟨5,_⟩ => exact repair12298Cell5
  | ⟨6,_⟩ => exact repair12298Cell6
  | ⟨7,_⟩ => exact repair12298Cell7
  | ⟨8,_⟩ => exact repair12298Cell8
  | ⟨9,_⟩ => exact repair12298Cell9
  | ⟨10,_⟩ => exact repair12298Cell10
  | ⟨11,_⟩ => exact repair12298Cell11
  | ⟨12,_⟩ => exact repair12298Cell12
  | ⟨13,_⟩ => exact repair12298Cell13
  | ⟨14,_⟩ => exact repair12298Cell14
  | ⟨15,_⟩ => exact repair12298Cell15
  | ⟨16,_⟩ => exact repair12298Cell16
  | ⟨17,_⟩ => exact repair12298Cell17
  | ⟨18,_⟩ => exact repair12298Cell18
  | ⟨19,_⟩ => exact repair12298Cell19
  | ⟨20,_⟩ => exact repair12298Cell20
  | ⟨21,_⟩ => exact repair12298Cell21
  | ⟨22,_⟩ => exact repair12298Cell22
  | ⟨23,_⟩ => exact repair12298Cell23
  | ⟨24,_⟩ => exact repair12298Cell24
  | ⟨25,_⟩ => exact repair12298Cell25
  | ⟨26,_⟩ => exact repair12298Cell26
  | ⟨27,_⟩ => exact repair12298Cell27
  | ⟨28,_⟩ => exact repair12298Cell28
  | ⟨29,_⟩ => exact repair12298Cell29
  | ⟨30,_⟩ => exact repair12298Cell30
  | ⟨31,_⟩ => exact repair12298Cell31
  | ⟨32,_⟩ => exact repair12298Cell32
  | ⟨33,_⟩ => exact repair12298Cell33
  | ⟨34,_⟩ => exact repair12298Cell34
  | ⟨35,_⟩ => exact repair12298Cell35
  | ⟨36,_⟩ => exact repair12298Cell36
  | ⟨37,_⟩ => exact repair12298Cell37
  | ⟨38,_⟩ => exact repair12298Cell38
  | ⟨39,_⟩ => exact repair12298Cell39
  | ⟨40,_⟩ => exact repair12298Cell40
  | ⟨41,_⟩ => exact repair12298Cell41
  | ⟨42,_⟩ => exact repair12298Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12298 : FrameRepair 12298 scalarRow12298 where
  cap := cap12298
  cap_nonneg := fun j => (repair12298Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12298])
  endpoint := fun j => (repair12298Cells j).2.1
  endpoint_upper := fun j => (repair12298Cells j).2.2.1
  frame := fun j => (repair12298Cells j).2.2.2

noncomputable def cap12299 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68986783 / 250000000 : ℝ)
  | ⟨1,_⟩ => (69087481 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276751721 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277152521 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (27755233 / 100000000 : ℝ)
  | ⟨5,_⟩ => (5559023 / 20000000 : ℝ)
  | ⟨6,_⟩ => (278348509 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139372681 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279141239 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (17471009 / 62500000 : ℝ)
  | ⟨10,_⟩ => (139965039 / 500000000 : ℝ)
  | ⟨11,_⟩ => (70080641 / 250000000 : ℝ)
  | ⟨12,_⟩ => (280714573 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140552567 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281495629 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (8808907 / 31250000 : ℝ)
  | ⟨16,_⟩ => (70568369 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282660997 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283047579 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283433233 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283817959 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (28420177 / 100000000 : ℝ)
  | ⟨22,_⟩ => (17786541 / 62500000 : ℝ)
  | ⟨23,_⟩ => (71241533 / 250000000 : ℝ)
  | ⟨24,_⟩ => (57069439 / 200000000 : ℝ)
  | ⟨25,_⟩ => (285726897 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (57221239 / 200000000 : ℝ)
  | ⟨27,_⟩ => (286484093 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (57372219 / 200000000 : ℝ)
  | ⟨29,_⟩ => (143618601 / 500000000 : ℝ)
  | ⟨30,_⟩ => (57522383 / 200000000 : ℝ)
  | ⟨31,_⟩ => (71996561 / 250000000 : ℝ)
  | ⟨32,_⟩ => (72089923 / 250000000 : ℝ)
  | ⟨33,_⟩ => (1154927 / 4000000 : ℝ)
  | ⟨34,_⟩ => (289102933 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72368311 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289842679 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145105627 / 500000000 : ℝ)
  | ⟨38,_⟩ => (58115793 / 200000000 : ℝ)
  | ⟨39,_⟩ => (290945303 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145655391 / 500000000 : ℝ)
  | ⟨41,_⟩ => (29167541 / 100000000 : ℝ)
  | ⟨42,_⟩ => (146019593 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12299Cell0 :
    0 ≤ cap12299 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨0,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12299 ⟨0,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨0,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell1 :
    0 ≤ cap12299 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨1,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12299 ⟨1,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨1,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell2 :
    0 ≤ cap12299 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨2,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12299 ⟨2,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨2,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell3 :
    0 ≤ cap12299 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨3,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12299 ⟨3,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨3,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell4 :
    0 ≤ cap12299 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨4,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12299 ⟨4,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨4,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell5 :
    0 ≤ cap12299 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨5,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12299 ⟨5,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨5,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell6 :
    0 ≤ cap12299 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨6,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12299 ⟨6,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨6,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell7 :
    0 ≤ cap12299 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨7,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12299 ⟨7,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨7,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell8 :
    0 ≤ cap12299 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨8,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12299 ⟨8,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨8,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell9 :
    0 ≤ cap12299 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨9,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12299 ⟨9,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨9,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell10 :
    0 ≤ cap12299 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨10,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12299 ⟨10,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨10,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell11 :
    0 ≤ cap12299 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨11,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12299 ⟨11,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨11,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell12 :
    0 ≤ cap12299 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨12,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12299 ⟨12,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨12,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell13 :
    0 ≤ cap12299 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨13,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12299 ⟨13,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨13,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell14 :
    0 ≤ cap12299 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨14,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12299 ⟨14,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨14,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell15 :
    0 ≤ cap12299 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨15,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12299 ⟨15,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨15,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell16 :
    0 ≤ cap12299 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨16,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12299 ⟨16,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨16,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell17 :
    0 ≤ cap12299 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨17,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12299 ⟨17,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨17,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell18 :
    0 ≤ cap12299 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨18,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12299 ⟨18,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨18,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell19 :
    0 ≤ cap12299 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨19,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12299 ⟨19,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨19,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell20 :
    0 ≤ cap12299 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨20,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12299 ⟨20,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨20,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell21 :
    0 ≤ cap12299 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨21,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12299 ⟨21,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨21,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell22 :
    0 ≤ cap12299 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨22,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12299 ⟨22,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨22,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell23 :
    0 ≤ cap12299 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨23,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12299 ⟨23,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨23,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell24 :
    0 ≤ cap12299 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨24,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12299 ⟨24,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨24,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell25 :
    0 ≤ cap12299 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨25,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12299 ⟨25,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨25,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell26 :
    0 ≤ cap12299 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨26,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12299 ⟨26,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨26,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell27 :
    0 ≤ cap12299 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨27,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12299 ⟨27,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨27,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell28 :
    0 ≤ cap12299 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨28,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12299 ⟨28,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨28,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell29 :
    0 ≤ cap12299 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨29,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12299 ⟨29,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨29,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell30 :
    0 ≤ cap12299 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨30,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12299 ⟨30,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨30,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell31 :
    0 ≤ cap12299 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨31,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12299 ⟨31,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨31,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell32 :
    0 ≤ cap12299 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨32,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12299 ⟨32,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨32,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell33 :
    0 ≤ cap12299 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨33,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12299 ⟨33,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨33,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell34 :
    0 ≤ cap12299 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨34,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12299 ⟨34,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨34,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell35 :
    0 ≤ cap12299 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨35,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12299 ⟨35,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨35,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell36 :
    0 ≤ cap12299 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨36,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12299 ⟨36,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨36,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell37 :
    0 ≤ cap12299 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨37,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12299 ⟨37,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨37,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell38 :
    0 ≤ cap12299 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨38,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12299 ⟨38,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨38,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell39 :
    0 ≤ cap12299 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨39,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12299 ⟨39,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨39,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell40 :
    0 ≤ cap12299 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨40,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12299 ⟨40,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨40,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell41 :
    0 ≤ cap12299 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨41,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12299 ⟨41,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨41,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cell42 :
    0 ≤ cap12299 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12299 (parameters ⟨42,by decide⟩)
      (scalarRow12299.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12299 ⟨42,by decide⟩ ∧
    (scalarRow12299.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 ⟨42,by decide⟩ + (scalarRow12299.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12299.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12299.targetFrame := by
  norm_num [cap12299, scalarRow12299, sourceIndex, cell12299, BstLean.Part263.envelope, parameters]

theorem repair12299Cells (j : Fin 43) :
    0 ≤ cap12299 j ∧
    BstLean.Part263.envelope 12299 (parameters j) (scalarRow12299.table (sourceIndex j)).upper ≤ cap12299 j ∧
    (scalarRow12299.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12299 j + (scalarRow12299.table (sourceIndex j)).centre) /
      (scalarRow12299.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12299.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12299Cell0
  | ⟨1,_⟩ => exact repair12299Cell1
  | ⟨2,_⟩ => exact repair12299Cell2
  | ⟨3,_⟩ => exact repair12299Cell3
  | ⟨4,_⟩ => exact repair12299Cell4
  | ⟨5,_⟩ => exact repair12299Cell5
  | ⟨6,_⟩ => exact repair12299Cell6
  | ⟨7,_⟩ => exact repair12299Cell7
  | ⟨8,_⟩ => exact repair12299Cell8
  | ⟨9,_⟩ => exact repair12299Cell9
  | ⟨10,_⟩ => exact repair12299Cell10
  | ⟨11,_⟩ => exact repair12299Cell11
  | ⟨12,_⟩ => exact repair12299Cell12
  | ⟨13,_⟩ => exact repair12299Cell13
  | ⟨14,_⟩ => exact repair12299Cell14
  | ⟨15,_⟩ => exact repair12299Cell15
  | ⟨16,_⟩ => exact repair12299Cell16
  | ⟨17,_⟩ => exact repair12299Cell17
  | ⟨18,_⟩ => exact repair12299Cell18
  | ⟨19,_⟩ => exact repair12299Cell19
  | ⟨20,_⟩ => exact repair12299Cell20
  | ⟨21,_⟩ => exact repair12299Cell21
  | ⟨22,_⟩ => exact repair12299Cell22
  | ⟨23,_⟩ => exact repair12299Cell23
  | ⟨24,_⟩ => exact repair12299Cell24
  | ⟨25,_⟩ => exact repair12299Cell25
  | ⟨26,_⟩ => exact repair12299Cell26
  | ⟨27,_⟩ => exact repair12299Cell27
  | ⟨28,_⟩ => exact repair12299Cell28
  | ⟨29,_⟩ => exact repair12299Cell29
  | ⟨30,_⟩ => exact repair12299Cell30
  | ⟨31,_⟩ => exact repair12299Cell31
  | ⟨32,_⟩ => exact repair12299Cell32
  | ⟨33,_⟩ => exact repair12299Cell33
  | ⟨34,_⟩ => exact repair12299Cell34
  | ⟨35,_⟩ => exact repair12299Cell35
  | ⟨36,_⟩ => exact repair12299Cell36
  | ⟨37,_⟩ => exact repair12299Cell37
  | ⟨38,_⟩ => exact repair12299Cell38
  | ⟨39,_⟩ => exact repair12299Cell39
  | ⟨40,_⟩ => exact repair12299Cell40
  | ⟨41,_⟩ => exact repair12299Cell41
  | ⟨42,_⟩ => exact repair12299Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12299 : FrameRepair 12299 scalarRow12299 where
  cap := cap12299
  cap_nonneg := fun j => (repair12299Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12299])
  endpoint := fun j => (repair12299Cells j).2.1
  endpoint_upper := fun j => (repair12299Cells j).2.2.1
  frame := fun j => (repair12299Cells j).2.2.2


end BstLean.Part264
