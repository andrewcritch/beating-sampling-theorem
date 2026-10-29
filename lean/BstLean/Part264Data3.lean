import BstLean.Part264Repair
/-! Rational envelope and frame checks for each dimension. -/
namespace BstLean.Part264
open Real Set BstLean.Part255 BstLean.Part263
noncomputable def cap12300 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275947057 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138174921 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276751633 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138576213 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277552229 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138975521 / 500000000 : ℝ)
  | ⟨6,_⟩ => (55669679 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278745241 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (34892639 / 125000000 : ℝ)
  | ⟨9,_⟩ => (279536011 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279929939 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280322419 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280714421 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (17569061 / 62500000 : ℝ)
  | ⟨14,_⟩ => (35186933 / 125000000 : ℝ)
  | ⟨15,_⟩ => (281884853 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282273299 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141330407 / 500000000 : ℝ)
  | ⟨18,_⟩ => (28304739 / 100000000 : ℝ)
  | ⟨19,_⟩ => (283433037 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283817757 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284201561 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142292221 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284965911 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (35668371 / 125000000 : ℝ)
  | ⟨25,_⟩ => (35715833 / 125000000 : ℝ)
  | ⟨26,_⟩ => (71526489 / 250000000 : ℝ)
  | ⟨27,_⟩ => (35810481 / 125000000 : ℝ)
  | ⟨28,_⟩ => (71715211 / 250000000 : ℝ)
  | ⟨29,_⟩ => (57447389 / 200000000 : ℝ)
  | ⟨30,_⟩ => (71902913 / 250000000 : ℝ)
  | ⟨31,_⟩ => (143992987 / 500000000 : ℝ)
  | ⟨32,_⟩ => (36044927 / 125000000 : ℝ)
  | ⟨33,_⟩ => (72182867 / 250000000 : ℝ)
  | ⟨34,_⟩ => (57820529 / 200000000 : ℝ)
  | ⟨35,_⟩ => (5789459 / 20000000 : ℝ)
  | ⟨36,_⟩ => (289842379 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (72552737 / 250000000 : ℝ)
  | ⟨38,_⟩ => (290578653 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (58188997 / 200000000 : ℝ)
  | ⟨40,_⟩ => (145655229 / 500000000 : ℝ)
  | ⟨41,_⟩ => (7291877 / 25000000 : ℝ)
  | ⟨42,_⟩ => (5840777 / 20000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12300Cell0 :
    0 ≤ cap12300 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨0,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12300 ⟨0,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨0,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell1 :
    0 ≤ cap12300 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨1,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12300 ⟨1,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨1,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell2 :
    0 ≤ cap12300 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨2,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12300 ⟨2,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨2,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell3 :
    0 ≤ cap12300 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨3,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12300 ⟨3,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨3,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell4 :
    0 ≤ cap12300 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨4,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12300 ⟨4,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨4,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell5 :
    0 ≤ cap12300 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨5,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12300 ⟨5,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨5,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell6 :
    0 ≤ cap12300 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨6,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12300 ⟨6,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨6,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell7 :
    0 ≤ cap12300 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨7,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12300 ⟨7,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨7,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell8 :
    0 ≤ cap12300 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨8,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12300 ⟨8,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨8,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell9 :
    0 ≤ cap12300 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨9,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12300 ⟨9,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨9,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell10 :
    0 ≤ cap12300 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨10,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12300 ⟨10,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨10,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell11 :
    0 ≤ cap12300 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨11,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12300 ⟨11,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨11,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell12 :
    0 ≤ cap12300 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨12,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12300 ⟨12,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨12,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell13 :
    0 ≤ cap12300 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨13,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12300 ⟨13,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨13,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell14 :
    0 ≤ cap12300 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨14,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12300 ⟨14,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨14,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell15 :
    0 ≤ cap12300 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨15,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12300 ⟨15,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨15,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell16 :
    0 ≤ cap12300 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨16,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12300 ⟨16,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨16,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell17 :
    0 ≤ cap12300 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨17,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12300 ⟨17,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨17,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell18 :
    0 ≤ cap12300 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨18,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12300 ⟨18,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨18,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell19 :
    0 ≤ cap12300 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨19,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12300 ⟨19,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨19,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell20 :
    0 ≤ cap12300 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨20,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12300 ⟨20,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨20,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell21 :
    0 ≤ cap12300 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨21,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12300 ⟨21,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨21,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell22 :
    0 ≤ cap12300 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨22,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12300 ⟨22,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨22,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell23 :
    0 ≤ cap12300 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨23,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12300 ⟨23,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨23,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell24 :
    0 ≤ cap12300 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨24,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12300 ⟨24,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨24,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell25 :
    0 ≤ cap12300 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨25,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12300 ⟨25,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨25,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell26 :
    0 ≤ cap12300 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨26,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12300 ⟨26,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨26,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell27 :
    0 ≤ cap12300 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨27,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12300 ⟨27,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨27,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell28 :
    0 ≤ cap12300 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨28,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12300 ⟨28,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨28,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell29 :
    0 ≤ cap12300 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨29,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12300 ⟨29,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨29,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell30 :
    0 ≤ cap12300 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨30,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12300 ⟨30,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨30,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell31 :
    0 ≤ cap12300 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨31,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12300 ⟨31,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨31,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell32 :
    0 ≤ cap12300 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨32,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12300 ⟨32,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨32,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell33 :
    0 ≤ cap12300 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨33,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12300 ⟨33,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨33,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell34 :
    0 ≤ cap12300 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨34,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12300 ⟨34,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨34,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell35 :
    0 ≤ cap12300 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨35,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12300 ⟨35,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨35,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell36 :
    0 ≤ cap12300 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨36,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12300 ⟨36,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨36,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell37 :
    0 ≤ cap12300 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨37,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12300 ⟨37,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨37,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell38 :
    0 ≤ cap12300 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨38,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12300 ⟨38,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨38,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell39 :
    0 ≤ cap12300 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨39,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12300 ⟨39,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨39,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell40 :
    0 ≤ cap12300 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨40,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12300 ⟨40,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨40,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell41 :
    0 ≤ cap12300 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨41,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12300 ⟨41,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨41,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cell42 :
    0 ≤ cap12300 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12300 (parameters ⟨42,by decide⟩)
      (scalarRow12300.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12300 ⟨42,by decide⟩ ∧
    (scalarRow12300.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 ⟨42,by decide⟩ + (scalarRow12300.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12300.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12300.targetFrame := by
  norm_num [cap12300, scalarRow12300, sourceIndex, cell12300, BstLean.Part263.envelope, parameters]

theorem repair12300Cells (j : Fin 43) :
    0 ≤ cap12300 j ∧
    BstLean.Part263.envelope 12300 (parameters j) (scalarRow12300.table (sourceIndex j)).upper ≤ cap12300 j ∧
    (scalarRow12300.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12300 j + (scalarRow12300.table (sourceIndex j)).centre) /
      (scalarRow12300.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12300.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12300Cell0
  | ⟨1,_⟩ => exact repair12300Cell1
  | ⟨2,_⟩ => exact repair12300Cell2
  | ⟨3,_⟩ => exact repair12300Cell3
  | ⟨4,_⟩ => exact repair12300Cell4
  | ⟨5,_⟩ => exact repair12300Cell5
  | ⟨6,_⟩ => exact repair12300Cell6
  | ⟨7,_⟩ => exact repair12300Cell7
  | ⟨8,_⟩ => exact repair12300Cell8
  | ⟨9,_⟩ => exact repair12300Cell9
  | ⟨10,_⟩ => exact repair12300Cell10
  | ⟨11,_⟩ => exact repair12300Cell11
  | ⟨12,_⟩ => exact repair12300Cell12
  | ⟨13,_⟩ => exact repair12300Cell13
  | ⟨14,_⟩ => exact repair12300Cell14
  | ⟨15,_⟩ => exact repair12300Cell15
  | ⟨16,_⟩ => exact repair12300Cell16
  | ⟨17,_⟩ => exact repair12300Cell17
  | ⟨18,_⟩ => exact repair12300Cell18
  | ⟨19,_⟩ => exact repair12300Cell19
  | ⟨20,_⟩ => exact repair12300Cell20
  | ⟨21,_⟩ => exact repair12300Cell21
  | ⟨22,_⟩ => exact repair12300Cell22
  | ⟨23,_⟩ => exact repair12300Cell23
  | ⟨24,_⟩ => exact repair12300Cell24
  | ⟨25,_⟩ => exact repair12300Cell25
  | ⟨26,_⟩ => exact repair12300Cell26
  | ⟨27,_⟩ => exact repair12300Cell27
  | ⟨28,_⟩ => exact repair12300Cell28
  | ⟨29,_⟩ => exact repair12300Cell29
  | ⟨30,_⟩ => exact repair12300Cell30
  | ⟨31,_⟩ => exact repair12300Cell31
  | ⟨32,_⟩ => exact repair12300Cell32
  | ⟨33,_⟩ => exact repair12300Cell33
  | ⟨34,_⟩ => exact repair12300Cell34
  | ⟨35,_⟩ => exact repair12300Cell35
  | ⟨36,_⟩ => exact repair12300Cell36
  | ⟨37,_⟩ => exact repair12300Cell37
  | ⟨38,_⟩ => exact repair12300Cell38
  | ⟨39,_⟩ => exact repair12300Cell39
  | ⟨40,_⟩ => exact repair12300Cell40
  | ⟨41,_⟩ => exact repair12300Cell41
  | ⟨42,_⟩ => exact repair12300Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12300 : FrameRepair 12300 scalarRow12300 where
  cap := cap12300
  cap_nonneg := fun j => (repair12300Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12300])
  endpoint := fun j => (repair12300Cells j).2.1
  endpoint_upper := fun j => (repair12300Cells j).2.2.1
  frame := fun j => (repair12300Cells j).2.2.2

noncomputable def cap12301 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137973491 / 500000000 : ℝ)
  | ⟨1,_⟩ => (863593 / 3125000 : ℝ)
  | ⟨2,_⟩ => (34593943 / 125000000 : ℝ)
  | ⟨3,_⟩ => (277152331 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (542094 / 1953125 : ℝ)
  | ⟨5,_⟩ => (55590187 / 200000000 : ℝ)
  | ⟨6,_⟩ => (278348281 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278745121 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139570493 / 500000000 : ℝ)
  | ⟨9,_⟩ => (139767939 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279929799 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280322273 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280714269 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140552409 / 500000000 : ℝ)
  | ⟨14,_⟩ => (2814953 / 10000000 : ℝ)
  | ⟨15,_⟩ => (140942341 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141136561 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282660631 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (353809 / 1250000 : ℝ)
  | ⟨19,_⟩ => (283432841 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (56763511 / 200000000 : ℝ)
  | ⟨21,_⟩ => (284201353 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284584227 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (28496569 / 100000000 : ℝ)
  | ⟨24,_⟩ => (285346741 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285726431 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286105717 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286483603 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286860593 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287236687 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (71902847 / 250000000 : ℝ)
  | ⟨31,_⟩ => (57597141 / 200000000 : ℝ)
  | ⟨32,_⟩ => (288359141 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144365593 / 500000000 : ℝ)
  | ⟨34,_⟩ => (289102357 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289472657 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289842079 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290210643 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290578341 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290944667 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58262027 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291674751 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (58407703 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12301Cell0 :
    0 ≤ cap12301 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨0,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12301 ⟨0,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨0,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell1 :
    0 ≤ cap12301 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨1,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12301 ⟨1,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨1,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell2 :
    0 ≤ cap12301 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨2,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12301 ⟨2,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨2,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell3 :
    0 ≤ cap12301 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨3,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12301 ⟨3,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨3,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell4 :
    0 ≤ cap12301 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨4,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12301 ⟨4,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨4,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell5 :
    0 ≤ cap12301 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨5,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12301 ⟨5,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨5,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell6 :
    0 ≤ cap12301 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨6,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12301 ⟨6,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨6,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell7 :
    0 ≤ cap12301 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨7,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12301 ⟨7,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨7,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell8 :
    0 ≤ cap12301 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨8,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12301 ⟨8,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨8,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell9 :
    0 ≤ cap12301 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨9,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12301 ⟨9,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨9,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell10 :
    0 ≤ cap12301 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨10,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12301 ⟨10,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨10,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell11 :
    0 ≤ cap12301 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨11,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12301 ⟨11,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨11,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell12 :
    0 ≤ cap12301 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨12,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12301 ⟨12,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨12,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell13 :
    0 ≤ cap12301 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨13,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12301 ⟨13,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨13,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell14 :
    0 ≤ cap12301 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨14,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12301 ⟨14,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨14,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell15 :
    0 ≤ cap12301 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨15,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12301 ⟨15,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨15,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell16 :
    0 ≤ cap12301 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨16,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12301 ⟨16,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨16,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell17 :
    0 ≤ cap12301 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨17,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12301 ⟨17,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨17,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell18 :
    0 ≤ cap12301 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨18,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12301 ⟨18,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨18,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell19 :
    0 ≤ cap12301 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨19,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12301 ⟨19,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨19,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell20 :
    0 ≤ cap12301 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨20,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12301 ⟨20,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨20,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell21 :
    0 ≤ cap12301 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨21,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12301 ⟨21,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨21,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell22 :
    0 ≤ cap12301 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨22,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12301 ⟨22,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨22,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell23 :
    0 ≤ cap12301 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨23,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12301 ⟨23,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨23,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell24 :
    0 ≤ cap12301 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨24,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12301 ⟨24,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨24,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell25 :
    0 ≤ cap12301 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨25,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12301 ⟨25,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨25,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell26 :
    0 ≤ cap12301 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨26,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12301 ⟨26,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨26,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell27 :
    0 ≤ cap12301 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨27,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12301 ⟨27,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨27,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell28 :
    0 ≤ cap12301 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨28,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12301 ⟨28,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨28,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell29 :
    0 ≤ cap12301 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨29,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12301 ⟨29,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨29,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell30 :
    0 ≤ cap12301 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨30,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12301 ⟨30,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨30,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell31 :
    0 ≤ cap12301 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨31,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12301 ⟨31,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨31,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell32 :
    0 ≤ cap12301 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨32,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12301 ⟨32,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨32,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell33 :
    0 ≤ cap12301 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨33,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12301 ⟨33,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨33,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell34 :
    0 ≤ cap12301 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨34,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12301 ⟨34,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨34,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell35 :
    0 ≤ cap12301 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨35,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12301 ⟨35,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨35,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell36 :
    0 ≤ cap12301 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨36,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12301 ⟨36,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨36,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell37 :
    0 ≤ cap12301 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨37,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12301 ⟨37,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨37,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell38 :
    0 ≤ cap12301 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨38,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12301 ⟨38,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨38,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell39 :
    0 ≤ cap12301 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨39,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12301 ⟨39,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨39,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell40 :
    0 ≤ cap12301 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨40,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12301 ⟨40,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨40,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell41 :
    0 ≤ cap12301 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨41,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12301 ⟨41,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨41,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cell42 :
    0 ≤ cap12301 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12301 (parameters ⟨42,by decide⟩)
      (scalarRow12301.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12301 ⟨42,by decide⟩ ∧
    (scalarRow12301.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 ⟨42,by decide⟩ + (scalarRow12301.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12301.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12301.targetFrame := by
  norm_num [cap12301, scalarRow12301, sourceIndex, cell12301, BstLean.Part263.envelope, parameters]

theorem repair12301Cells (j : Fin 43) :
    0 ≤ cap12301 j ∧
    BstLean.Part263.envelope 12301 (parameters j) (scalarRow12301.table (sourceIndex j)).upper ≤ cap12301 j ∧
    (scalarRow12301.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12301 j + (scalarRow12301.table (sourceIndex j)).centre) /
      (scalarRow12301.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12301.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12301Cell0
  | ⟨1,_⟩ => exact repair12301Cell1
  | ⟨2,_⟩ => exact repair12301Cell2
  | ⟨3,_⟩ => exact repair12301Cell3
  | ⟨4,_⟩ => exact repair12301Cell4
  | ⟨5,_⟩ => exact repair12301Cell5
  | ⟨6,_⟩ => exact repair12301Cell6
  | ⟨7,_⟩ => exact repair12301Cell7
  | ⟨8,_⟩ => exact repair12301Cell8
  | ⟨9,_⟩ => exact repair12301Cell9
  | ⟨10,_⟩ => exact repair12301Cell10
  | ⟨11,_⟩ => exact repair12301Cell11
  | ⟨12,_⟩ => exact repair12301Cell12
  | ⟨13,_⟩ => exact repair12301Cell13
  | ⟨14,_⟩ => exact repair12301Cell14
  | ⟨15,_⟩ => exact repair12301Cell15
  | ⟨16,_⟩ => exact repair12301Cell16
  | ⟨17,_⟩ => exact repair12301Cell17
  | ⟨18,_⟩ => exact repair12301Cell18
  | ⟨19,_⟩ => exact repair12301Cell19
  | ⟨20,_⟩ => exact repair12301Cell20
  | ⟨21,_⟩ => exact repair12301Cell21
  | ⟨22,_⟩ => exact repair12301Cell22
  | ⟨23,_⟩ => exact repair12301Cell23
  | ⟨24,_⟩ => exact repair12301Cell24
  | ⟨25,_⟩ => exact repair12301Cell25
  | ⟨26,_⟩ => exact repair12301Cell26
  | ⟨27,_⟩ => exact repair12301Cell27
  | ⟨28,_⟩ => exact repair12301Cell28
  | ⟨29,_⟩ => exact repair12301Cell29
  | ⟨30,_⟩ => exact repair12301Cell30
  | ⟨31,_⟩ => exact repair12301Cell31
  | ⟨32,_⟩ => exact repair12301Cell32
  | ⟨33,_⟩ => exact repair12301Cell33
  | ⟨34,_⟩ => exact repair12301Cell34
  | ⟨35,_⟩ => exact repair12301Cell35
  | ⟨36,_⟩ => exact repair12301Cell36
  | ⟨37,_⟩ => exact repair12301Cell37
  | ⟨38,_⟩ => exact repair12301Cell38
  | ⟨39,_⟩ => exact repair12301Cell39
  | ⟨40,_⟩ => exact repair12301Cell40
  | ⟨41,_⟩ => exact repair12301Cell41
  | ⟨42,_⟩ => exact repair12301Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12301 : FrameRepair 12301 scalarRow12301 where
  cap := cap12301
  cap_nonneg := fun j => (repair12301Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12301])
  endpoint := fun j => (repair12301Cells j).2.1
  endpoint_upper := fun j => (repair12301Cells j).2.2.1
  frame := fun j => (repair12301Cells j).2.2.2

noncomputable def cap12302 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137973453 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138174839 / 500000000 : ℝ)
  | ⟨2,_⟩ => (8648483 / 31250000 : ℝ)
  | ⟨3,_⟩ => (69288059 / 250000000 : ℝ)
  | ⟨4,_⟩ => (277552027 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277950827 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278348167 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278745001 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279140859 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55907149 / 200000000 : ℝ)
  | ⟨10,_⟩ => (13996483 / 50000000 : ℝ)
  | ⟨11,_⟩ => (280322127 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280714117 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281104659 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (56299027 / 200000000 : ℝ)
  | ⟨15,_⟩ => (281884511 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (56454589 / 200000000 : ℝ)
  | ⟨17,_⟩ => (282660447 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (28304701 / 100000000 : ℝ)
  | ⟨19,_⟩ => (56686529 / 200000000 : ℝ)
  | ⟨20,_⟩ => (283817353 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56840229 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284584013 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (28496547 / 100000000 : ℝ)
  | ⟨24,_⟩ => (142673257 / 500000000 : ℝ)
  | ⟨25,_⟩ => (142863099 / 500000000 : ℝ)
  | ⟨26,_⟩ => (143052739 / 500000000 : ℝ)
  | ⟨27,_⟩ => (143241679 / 500000000 : ℝ)
  | ⟨28,_⟩ => (143430171 / 500000000 : ℝ)
  | ⟨29,_⟩ => (28723643 / 100000000 : ℝ)
  | ⟨30,_⟩ => (2300889 / 8000000 : ℝ)
  | ⟨31,_⟩ => (57597087 / 200000000 : ℝ)
  | ⟨32,_⟩ => (57671773 / 200000000 : ℝ)
  | ⟨33,_⟩ => (57746181 / 200000000 : ℝ)
  | ⟨34,_⟩ => (28910207 / 100000000 : ℝ)
  | ⟨35,_⟩ => (289472363 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (14492089 / 50000000 : ℝ)
  | ⟨37,_⟩ => (290210337 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (29057803 / 100000000 : ℝ)
  | ⟨39,_⟩ => (5818887 / 20000000 : ℝ)
  | ⟨40,_⟩ => (291309811 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291674421 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (14601909 / 50000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12302Cell0 :
    0 ≤ cap12302 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨0,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12302 ⟨0,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨0,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell1 :
    0 ≤ cap12302 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨1,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12302 ⟨1,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨1,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell2 :
    0 ≤ cap12302 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨2,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12302 ⟨2,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨2,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell3 :
    0 ≤ cap12302 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨3,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12302 ⟨3,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨3,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell4 :
    0 ≤ cap12302 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨4,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12302 ⟨4,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨4,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell5 :
    0 ≤ cap12302 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨5,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12302 ⟨5,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨5,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell6 :
    0 ≤ cap12302 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨6,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12302 ⟨6,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨6,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell7 :
    0 ≤ cap12302 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨7,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12302 ⟨7,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨7,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell8 :
    0 ≤ cap12302 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨8,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12302 ⟨8,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨8,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell9 :
    0 ≤ cap12302 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨9,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12302 ⟨9,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨9,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell10 :
    0 ≤ cap12302 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨10,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12302 ⟨10,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨10,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell11 :
    0 ≤ cap12302 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨11,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12302 ⟨11,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨11,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell12 :
    0 ≤ cap12302 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨12,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12302 ⟨12,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨12,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell13 :
    0 ≤ cap12302 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨13,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12302 ⟨13,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨13,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell14 :
    0 ≤ cap12302 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨14,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12302 ⟨14,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨14,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell15 :
    0 ≤ cap12302 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨15,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12302 ⟨15,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨15,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell16 :
    0 ≤ cap12302 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨16,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12302 ⟨16,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨16,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell17 :
    0 ≤ cap12302 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨17,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12302 ⟨17,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨17,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell18 :
    0 ≤ cap12302 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨18,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12302 ⟨18,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨18,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell19 :
    0 ≤ cap12302 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨19,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12302 ⟨19,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨19,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell20 :
    0 ≤ cap12302 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨20,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12302 ⟨20,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨20,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell21 :
    0 ≤ cap12302 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨21,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12302 ⟨21,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨21,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell22 :
    0 ≤ cap12302 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨22,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12302 ⟨22,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨22,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell23 :
    0 ≤ cap12302 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨23,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12302 ⟨23,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨23,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell24 :
    0 ≤ cap12302 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨24,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12302 ⟨24,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨24,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell25 :
    0 ≤ cap12302 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨25,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12302 ⟨25,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨25,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell26 :
    0 ≤ cap12302 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨26,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12302 ⟨26,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨26,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell27 :
    0 ≤ cap12302 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨27,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12302 ⟨27,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨27,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell28 :
    0 ≤ cap12302 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨28,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12302 ⟨28,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨28,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell29 :
    0 ≤ cap12302 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨29,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12302 ⟨29,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨29,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell30 :
    0 ≤ cap12302 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨30,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12302 ⟨30,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨30,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell31 :
    0 ≤ cap12302 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨31,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12302 ⟨31,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨31,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell32 :
    0 ≤ cap12302 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨32,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12302 ⟨32,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨32,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell33 :
    0 ≤ cap12302 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨33,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12302 ⟨33,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨33,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell34 :
    0 ≤ cap12302 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨34,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12302 ⟨34,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨34,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell35 :
    0 ≤ cap12302 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨35,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12302 ⟨35,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨35,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell36 :
    0 ≤ cap12302 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨36,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12302 ⟨36,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨36,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell37 :
    0 ≤ cap12302 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨37,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12302 ⟨37,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨37,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell38 :
    0 ≤ cap12302 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨38,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12302 ⟨38,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨38,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell39 :
    0 ≤ cap12302 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨39,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12302 ⟨39,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨39,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell40 :
    0 ≤ cap12302 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨40,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12302 ⟨40,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨40,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell41 :
    0 ≤ cap12302 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨41,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12302 ⟨41,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨41,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cell42 :
    0 ≤ cap12302 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12302 (parameters ⟨42,by decide⟩)
      (scalarRow12302.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12302 ⟨42,by decide⟩ ∧
    (scalarRow12302.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 ⟨42,by decide⟩ + (scalarRow12302.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12302.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12302.targetFrame := by
  norm_num [cap12302, scalarRow12302, sourceIndex, cell12302, BstLean.Part263.envelope, parameters]

theorem repair12302Cells (j : Fin 43) :
    0 ≤ cap12302 j ∧
    BstLean.Part263.envelope 12302 (parameters j) (scalarRow12302.table (sourceIndex j)).upper ≤ cap12302 j ∧
    (scalarRow12302.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12302 j + (scalarRow12302.table (sourceIndex j)).centre) /
      (scalarRow12302.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12302.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12302Cell0
  | ⟨1,_⟩ => exact repair12302Cell1
  | ⟨2,_⟩ => exact repair12302Cell2
  | ⟨3,_⟩ => exact repair12302Cell3
  | ⟨4,_⟩ => exact repair12302Cell4
  | ⟨5,_⟩ => exact repair12302Cell5
  | ⟨6,_⟩ => exact repair12302Cell6
  | ⟨7,_⟩ => exact repair12302Cell7
  | ⟨8,_⟩ => exact repair12302Cell8
  | ⟨9,_⟩ => exact repair12302Cell9
  | ⟨10,_⟩ => exact repair12302Cell10
  | ⟨11,_⟩ => exact repair12302Cell11
  | ⟨12,_⟩ => exact repair12302Cell12
  | ⟨13,_⟩ => exact repair12302Cell13
  | ⟨14,_⟩ => exact repair12302Cell14
  | ⟨15,_⟩ => exact repair12302Cell15
  | ⟨16,_⟩ => exact repair12302Cell16
  | ⟨17,_⟩ => exact repair12302Cell17
  | ⟨18,_⟩ => exact repair12302Cell18
  | ⟨19,_⟩ => exact repair12302Cell19
  | ⟨20,_⟩ => exact repair12302Cell20
  | ⟨21,_⟩ => exact repair12302Cell21
  | ⟨22,_⟩ => exact repair12302Cell22
  | ⟨23,_⟩ => exact repair12302Cell23
  | ⟨24,_⟩ => exact repair12302Cell24
  | ⟨25,_⟩ => exact repair12302Cell25
  | ⟨26,_⟩ => exact repair12302Cell26
  | ⟨27,_⟩ => exact repair12302Cell27
  | ⟨28,_⟩ => exact repair12302Cell28
  | ⟨29,_⟩ => exact repair12302Cell29
  | ⟨30,_⟩ => exact repair12302Cell30
  | ⟨31,_⟩ => exact repair12302Cell31
  | ⟨32,_⟩ => exact repair12302Cell32
  | ⟨33,_⟩ => exact repair12302Cell33
  | ⟨34,_⟩ => exact repair12302Cell34
  | ⟨35,_⟩ => exact repair12302Cell35
  | ⟨36,_⟩ => exact repair12302Cell36
  | ⟨37,_⟩ => exact repair12302Cell37
  | ⟨38,_⟩ => exact repair12302Cell38
  | ⟨39,_⟩ => exact repair12302Cell39
  | ⟨40,_⟩ => exact repair12302Cell40
  | ⟨41,_⟩ => exact repair12302Cell41
  | ⟨42,_⟩ => exact repair12302Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12302 : FrameRepair 12302 scalarRow12302 where
  cap := cap12302
  cap_nonneg := fun j => (repair12302Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12302])
  endpoint := fun j => (repair12302Cells j).2.1
  endpoint_upper := fun j => (repair12302Cells j).2.2.1
  frame := fun j => (repair12302Cells j).2.2.2

noncomputable def cap12303 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275946831 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276349597 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (34593921 / 125000000 : ℝ)
  | ⟨3,_⟩ => (138576071 / 500000000 : ℝ)
  | ⟨4,_⟩ => (138775963 / 500000000 : ℝ)
  | ⟨5,_⟩ => (217149 / 781250 : ℝ)
  | ⟨6,_⟩ => (278348053 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278744881 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (69785183 / 250000000 : ℝ)
  | ⟨9,_⟩ => (69883903 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279929521 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280321981 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (56142793 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281104501 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281494971 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (14094217 / 50000000 : ℝ)
  | ⟨16,_⟩ => (551314 / 1953125 : ℝ)
  | ⟨17,_⟩ => (35332533 / 125000000 : ℝ)
  | ⟨18,_⟩ => (283046821 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283432449 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283817151 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284200937 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142291899 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284965249 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (17834143 / 62500000 : ℝ)
  | ⟨25,_⟩ => (57145193 / 200000000 : ℝ)
  | ⟨26,_⟩ => (286105239 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286483113 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (28686009 / 100000000 : ℝ)
  | ⟨29,_⟩ => (71809043 / 250000000 : ℝ)
  | ⟨30,_⟩ => (287610861 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143992583 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288358589 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288730623 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144550891 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289472069 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (7246037 / 25000000 : ℝ)
  | ⟨37,_⟩ => (290210031 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145288859 / 500000000 : ℝ)
  | ⟨39,_⟩ => (9092001 / 31250000 : ℝ)
  | ⟨40,_⟩ => (18206843 / 62500000 : ℝ)
  | ⟨41,_⟩ => (72918523 / 250000000 : ℝ)
  | ⟨42,_⟩ => (73009461 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12303Cell0 :
    0 ≤ cap12303 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨0,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12303 ⟨0,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨0,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell1 :
    0 ≤ cap12303 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨1,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12303 ⟨1,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨1,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell2 :
    0 ≤ cap12303 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨2,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12303 ⟨2,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨2,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell3 :
    0 ≤ cap12303 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨3,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12303 ⟨3,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨3,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell4 :
    0 ≤ cap12303 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨4,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12303 ⟨4,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨4,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell5 :
    0 ≤ cap12303 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨5,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12303 ⟨5,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨5,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell6 :
    0 ≤ cap12303 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨6,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12303 ⟨6,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨6,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell7 :
    0 ≤ cap12303 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨7,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12303 ⟨7,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨7,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell8 :
    0 ≤ cap12303 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨8,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12303 ⟨8,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨8,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell9 :
    0 ≤ cap12303 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨9,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12303 ⟨9,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨9,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell10 :
    0 ≤ cap12303 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨10,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12303 ⟨10,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨10,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell11 :
    0 ≤ cap12303 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨11,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12303 ⟨11,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨11,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell12 :
    0 ≤ cap12303 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨12,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12303 ⟨12,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨12,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell13 :
    0 ≤ cap12303 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨13,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12303 ⟨13,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨13,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell14 :
    0 ≤ cap12303 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨14,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12303 ⟨14,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨14,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell15 :
    0 ≤ cap12303 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨15,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12303 ⟨15,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨15,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell16 :
    0 ≤ cap12303 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨16,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12303 ⟨16,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨16,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell17 :
    0 ≤ cap12303 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨17,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12303 ⟨17,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨17,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell18 :
    0 ≤ cap12303 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨18,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12303 ⟨18,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨18,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell19 :
    0 ≤ cap12303 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨19,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12303 ⟨19,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨19,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell20 :
    0 ≤ cap12303 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨20,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12303 ⟨20,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨20,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell21 :
    0 ≤ cap12303 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨21,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12303 ⟨21,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨21,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell22 :
    0 ≤ cap12303 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨22,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12303 ⟨22,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨22,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell23 :
    0 ≤ cap12303 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨23,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12303 ⟨23,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨23,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell24 :
    0 ≤ cap12303 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨24,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12303 ⟨24,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨24,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell25 :
    0 ≤ cap12303 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨25,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12303 ⟨25,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨25,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell26 :
    0 ≤ cap12303 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨26,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12303 ⟨26,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨26,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell27 :
    0 ≤ cap12303 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨27,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12303 ⟨27,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨27,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell28 :
    0 ≤ cap12303 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨28,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12303 ⟨28,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨28,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell29 :
    0 ≤ cap12303 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨29,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12303 ⟨29,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨29,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell30 :
    0 ≤ cap12303 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨30,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12303 ⟨30,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨30,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell31 :
    0 ≤ cap12303 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨31,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12303 ⟨31,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨31,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell32 :
    0 ≤ cap12303 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨32,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12303 ⟨32,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨32,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell33 :
    0 ≤ cap12303 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨33,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12303 ⟨33,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨33,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell34 :
    0 ≤ cap12303 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨34,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12303 ⟨34,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨34,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell35 :
    0 ≤ cap12303 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨35,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12303 ⟨35,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨35,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell36 :
    0 ≤ cap12303 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨36,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12303 ⟨36,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨36,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell37 :
    0 ≤ cap12303 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨37,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12303 ⟨37,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨37,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell38 :
    0 ≤ cap12303 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨38,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12303 ⟨38,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨38,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell39 :
    0 ≤ cap12303 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨39,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12303 ⟨39,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨39,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell40 :
    0 ≤ cap12303 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨40,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12303 ⟨40,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨40,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell41 :
    0 ≤ cap12303 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨41,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12303 ⟨41,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨41,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cell42 :
    0 ≤ cap12303 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12303 (parameters ⟨42,by decide⟩)
      (scalarRow12303.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12303 ⟨42,by decide⟩ ∧
    (scalarRow12303.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 ⟨42,by decide⟩ + (scalarRow12303.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12303.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12303.targetFrame := by
  norm_num [cap12303, scalarRow12303, sourceIndex, cell12303, BstLean.Part263.envelope, parameters]

theorem repair12303Cells (j : Fin 43) :
    0 ≤ cap12303 j ∧
    BstLean.Part263.envelope 12303 (parameters j) (scalarRow12303.table (sourceIndex j)).upper ≤ cap12303 j ∧
    (scalarRow12303.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12303 j + (scalarRow12303.table (sourceIndex j)).centre) /
      (scalarRow12303.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12303.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12303Cell0
  | ⟨1,_⟩ => exact repair12303Cell1
  | ⟨2,_⟩ => exact repair12303Cell2
  | ⟨3,_⟩ => exact repair12303Cell3
  | ⟨4,_⟩ => exact repair12303Cell4
  | ⟨5,_⟩ => exact repair12303Cell5
  | ⟨6,_⟩ => exact repair12303Cell6
  | ⟨7,_⟩ => exact repair12303Cell7
  | ⟨8,_⟩ => exact repair12303Cell8
  | ⟨9,_⟩ => exact repair12303Cell9
  | ⟨10,_⟩ => exact repair12303Cell10
  | ⟨11,_⟩ => exact repair12303Cell11
  | ⟨12,_⟩ => exact repair12303Cell12
  | ⟨13,_⟩ => exact repair12303Cell13
  | ⟨14,_⟩ => exact repair12303Cell14
  | ⟨15,_⟩ => exact repair12303Cell15
  | ⟨16,_⟩ => exact repair12303Cell16
  | ⟨17,_⟩ => exact repair12303Cell17
  | ⟨18,_⟩ => exact repair12303Cell18
  | ⟨19,_⟩ => exact repair12303Cell19
  | ⟨20,_⟩ => exact repair12303Cell20
  | ⟨21,_⟩ => exact repair12303Cell21
  | ⟨22,_⟩ => exact repair12303Cell22
  | ⟨23,_⟩ => exact repair12303Cell23
  | ⟨24,_⟩ => exact repair12303Cell24
  | ⟨25,_⟩ => exact repair12303Cell25
  | ⟨26,_⟩ => exact repair12303Cell26
  | ⟨27,_⟩ => exact repair12303Cell27
  | ⟨28,_⟩ => exact repair12303Cell28
  | ⟨29,_⟩ => exact repair12303Cell29
  | ⟨30,_⟩ => exact repair12303Cell30
  | ⟨31,_⟩ => exact repair12303Cell31
  | ⟨32,_⟩ => exact repair12303Cell32
  | ⟨33,_⟩ => exact repair12303Cell33
  | ⟨34,_⟩ => exact repair12303Cell34
  | ⟨35,_⟩ => exact repair12303Cell35
  | ⟨36,_⟩ => exact repair12303Cell36
  | ⟨37,_⟩ => exact repair12303Cell37
  | ⟨38,_⟩ => exact repair12303Cell38
  | ⟨39,_⟩ => exact repair12303Cell39
  | ⟨40,_⟩ => exact repair12303Cell40
  | ⟨41,_⟩ => exact repair12303Cell41
  | ⟨42,_⟩ => exact repair12303Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12303 : FrameRepair 12303 scalarRow12303 where
  cap := cap12303
  cap_nonneg := fun j => (repair12303Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12303])
  endpoint := fun j => (repair12303Cells j).2.1
  endpoint_upper := fun j => (repair12303Cells j).2.2.1
  frame := fun j => (repair12303Cells j).2.2.2

noncomputable def cap12304 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68986689 / 250000000 : ℝ)
  | ⟨1,_⟩ => (55269903 / 200000000 : ℝ)
  | ⟨2,_⟩ => (3459391 / 12500000 : ℝ)
  | ⟨3,_⟩ => (277152047 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (11102073 / 40000000 : ℝ)
  | ⟨5,_⟩ => (69487653 / 250000000 : ℝ)
  | ⟨6,_⟩ => (278347939 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (6968619 / 25000000 : ℝ)
  | ⟨8,_⟩ => (139570303 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279535479 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279929381 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (70080459 / 250000000 : ℝ)
  | ⟨12,_⟩ => (280713813 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281104343 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140747403 / 500000000 : ℝ)
  | ⟨15,_⟩ => (28188417 / 100000000 : ℝ)
  | ⟨16,_⟩ => (282272591 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (3533251 / 12500000 : ℝ)
  | ⟨18,_⟩ => (283046631 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141716127 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283816949 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (35525091 / 125000000 : ℝ)
  | ⟨22,_⟩ => (8893237 / 31250000 : ℝ)
  | ⟨23,_⟩ => (284965029 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285346061 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (71431433 / 250000000 : ℝ)
  | ⟨26,_⟩ => (57221 / 200000 : ℝ)
  | ⟨27,_⟩ => (286482867 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286859839 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (57447183 / 200000000 : ℝ)
  | ⟨30,_⟩ => (143805299 / 500000000 : ℝ)
  | ⟨31,_⟩ => (1124941 / 3906250 : ℝ)
  | ⟨32,_⟩ => (144179157 / 500000000 : ℝ)
  | ⟨33,_⟩ => (144365171 / 500000000 : ℝ)
  | ⟨34,_⟩ => (144550747 / 500000000 : ℝ)
  | ⟨35,_⟩ => (9045993 / 31250000 : ℝ)
  | ⟨36,_⟩ => (14492059 / 50000000 : ℝ)
  | ⟨37,_⟩ => (145104863 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145288703 / 500000000 : ℝ)
  | ⟨39,_⟩ => (58188743 / 200000000 : ℝ)
  | ⟨40,_⟩ => (72827291 / 250000000 : ℝ)
  | ⟨41,_⟩ => (145836881 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292037509 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12304Cell0 :
    0 ≤ cap12304 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨0,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12304 ⟨0,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨0,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell1 :
    0 ≤ cap12304 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨1,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12304 ⟨1,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨1,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell2 :
    0 ≤ cap12304 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨2,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12304 ⟨2,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨2,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell3 :
    0 ≤ cap12304 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨3,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12304 ⟨3,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨3,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell4 :
    0 ≤ cap12304 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨4,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12304 ⟨4,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨4,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell5 :
    0 ≤ cap12304 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨5,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12304 ⟨5,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨5,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell6 :
    0 ≤ cap12304 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨6,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12304 ⟨6,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨6,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell7 :
    0 ≤ cap12304 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨7,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12304 ⟨7,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨7,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell8 :
    0 ≤ cap12304 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨8,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12304 ⟨8,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨8,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell9 :
    0 ≤ cap12304 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨9,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12304 ⟨9,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨9,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell10 :
    0 ≤ cap12304 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨10,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12304 ⟨10,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨10,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell11 :
    0 ≤ cap12304 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨11,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12304 ⟨11,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨11,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell12 :
    0 ≤ cap12304 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨12,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12304 ⟨12,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨12,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell13 :
    0 ≤ cap12304 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨13,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12304 ⟨13,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨13,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell14 :
    0 ≤ cap12304 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨14,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12304 ⟨14,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨14,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell15 :
    0 ≤ cap12304 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨15,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12304 ⟨15,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨15,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell16 :
    0 ≤ cap12304 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨16,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12304 ⟨16,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨16,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell17 :
    0 ≤ cap12304 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨17,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12304 ⟨17,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨17,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell18 :
    0 ≤ cap12304 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨18,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12304 ⟨18,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨18,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell19 :
    0 ≤ cap12304 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨19,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12304 ⟨19,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨19,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell20 :
    0 ≤ cap12304 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨20,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12304 ⟨20,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨20,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell21 :
    0 ≤ cap12304 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨21,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12304 ⟨21,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨21,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell22 :
    0 ≤ cap12304 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨22,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12304 ⟨22,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨22,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell23 :
    0 ≤ cap12304 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨23,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12304 ⟨23,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨23,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell24 :
    0 ≤ cap12304 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨24,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12304 ⟨24,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨24,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell25 :
    0 ≤ cap12304 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨25,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12304 ⟨25,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨25,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell26 :
    0 ≤ cap12304 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨26,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12304 ⟨26,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨26,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell27 :
    0 ≤ cap12304 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨27,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12304 ⟨27,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨27,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell28 :
    0 ≤ cap12304 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨28,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12304 ⟨28,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨28,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell29 :
    0 ≤ cap12304 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨29,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12304 ⟨29,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨29,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell30 :
    0 ≤ cap12304 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨30,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12304 ⟨30,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨30,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell31 :
    0 ≤ cap12304 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨31,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12304 ⟨31,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨31,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell32 :
    0 ≤ cap12304 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨32,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12304 ⟨32,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨32,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell33 :
    0 ≤ cap12304 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨33,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12304 ⟨33,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨33,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell34 :
    0 ≤ cap12304 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨34,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12304 ⟨34,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨34,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell35 :
    0 ≤ cap12304 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨35,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12304 ⟨35,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨35,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell36 :
    0 ≤ cap12304 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨36,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12304 ⟨36,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨36,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell37 :
    0 ≤ cap12304 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨37,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12304 ⟨37,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨37,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell38 :
    0 ≤ cap12304 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨38,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12304 ⟨38,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨38,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell39 :
    0 ≤ cap12304 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨39,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12304 ⟨39,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨39,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell40 :
    0 ≤ cap12304 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨40,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12304 ⟨40,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨40,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell41 :
    0 ≤ cap12304 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨41,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12304 ⟨41,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨41,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cell42 :
    0 ≤ cap12304 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12304 (parameters ⟨42,by decide⟩)
      (scalarRow12304.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12304 ⟨42,by decide⟩ ∧
    (scalarRow12304.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 ⟨42,by decide⟩ + (scalarRow12304.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12304.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12304.targetFrame := by
  norm_num [cap12304, scalarRow12304, sourceIndex, cell12304, BstLean.Part263.envelope, parameters]

theorem repair12304Cells (j : Fin 43) :
    0 ≤ cap12304 j ∧
    BstLean.Part263.envelope 12304 (parameters j) (scalarRow12304.table (sourceIndex j)).upper ≤ cap12304 j ∧
    (scalarRow12304.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12304 j + (scalarRow12304.table (sourceIndex j)).centre) /
      (scalarRow12304.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12304.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12304Cell0
  | ⟨1,_⟩ => exact repair12304Cell1
  | ⟨2,_⟩ => exact repair12304Cell2
  | ⟨3,_⟩ => exact repair12304Cell3
  | ⟨4,_⟩ => exact repair12304Cell4
  | ⟨5,_⟩ => exact repair12304Cell5
  | ⟨6,_⟩ => exact repair12304Cell6
  | ⟨7,_⟩ => exact repair12304Cell7
  | ⟨8,_⟩ => exact repair12304Cell8
  | ⟨9,_⟩ => exact repair12304Cell9
  | ⟨10,_⟩ => exact repair12304Cell10
  | ⟨11,_⟩ => exact repair12304Cell11
  | ⟨12,_⟩ => exact repair12304Cell12
  | ⟨13,_⟩ => exact repair12304Cell13
  | ⟨14,_⟩ => exact repair12304Cell14
  | ⟨15,_⟩ => exact repair12304Cell15
  | ⟨16,_⟩ => exact repair12304Cell16
  | ⟨17,_⟩ => exact repair12304Cell17
  | ⟨18,_⟩ => exact repair12304Cell18
  | ⟨19,_⟩ => exact repair12304Cell19
  | ⟨20,_⟩ => exact repair12304Cell20
  | ⟨21,_⟩ => exact repair12304Cell21
  | ⟨22,_⟩ => exact repair12304Cell22
  | ⟨23,_⟩ => exact repair12304Cell23
  | ⟨24,_⟩ => exact repair12304Cell24
  | ⟨25,_⟩ => exact repair12304Cell25
  | ⟨26,_⟩ => exact repair12304Cell26
  | ⟨27,_⟩ => exact repair12304Cell27
  | ⟨28,_⟩ => exact repair12304Cell28
  | ⟨29,_⟩ => exact repair12304Cell29
  | ⟨30,_⟩ => exact repair12304Cell30
  | ⟨31,_⟩ => exact repair12304Cell31
  | ⟨32,_⟩ => exact repair12304Cell32
  | ⟨33,_⟩ => exact repair12304Cell33
  | ⟨34,_⟩ => exact repair12304Cell34
  | ⟨35,_⟩ => exact repair12304Cell35
  | ⟨36,_⟩ => exact repair12304Cell36
  | ⟨37,_⟩ => exact repair12304Cell37
  | ⟨38,_⟩ => exact repair12304Cell38
  | ⟨39,_⟩ => exact repair12304Cell39
  | ⟨40,_⟩ => exact repair12304Cell40
  | ⟨41,_⟩ => exact repair12304Cell41
  | ⟨42,_⟩ => exact repair12304Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12304 : FrameRepair 12304 scalarRow12304 where
  cap := cap12304
  cap_nonneg := fun j => (repair12304Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12304])
  endpoint := fun j => (repair12304Cells j).2.1
  endpoint_upper := fun j => (repair12304Cells j).2.2.1
  frame := fun j => (repair12304Cells j).2.2.2

noncomputable def cap12305 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275946681 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276349433 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (34593899 / 125000000 : ℝ)
  | ⟨3,_⟩ => (277151953 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277551723 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (55590101 / 200000000 : ℝ)
  | ⟨6,_⟩ => (11133913 / 40000000 : ℝ)
  | ⟨7,_⟩ => (871077 / 3125000 : ℝ)
  | ⟨8,_⟩ => (279140479 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139767673 / 500000000 : ℝ)
  | ⟨10,_⟩ => (139964621 / 500000000 : ℝ)
  | ⟨11,_⟩ => (28032169 / 100000000 : ℝ)
  | ⟨12,_⟩ => (280713661 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (56220837 / 200000000 : ℝ)
  | ⟨14,_⟩ => (281494641 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281883999 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (141136207 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282659897 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141523221 / 500000000 : ℝ)
  | ⟨19,_⟩ => (141716029 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283816747 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (7105013 / 25000000 : ℝ)
  | ⟨22,_⟩ => (284583369 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (35620601 / 125000000 : ℝ)
  | ⟨24,_⟩ => (142672917 / 500000000 : ℝ)
  | ⟨25,_⟩ => (571451 / 2000000 : ℝ)
  | ⟨26,_⟩ => (286104761 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143241311 / 500000000 : ℝ)
  | ⟨28,_⟩ => (71714897 / 250000000 : ℝ)
  | ⟨29,_⟩ => (143617829 / 500000000 : ℝ)
  | ⟨30,_⟩ => (143805167 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287984627 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (144179019 / 500000000 : ℝ)
  | ⟨33,_⟩ => (14436503 / 50000000 : ℝ)
  | ⟨34,_⟩ => (289101207 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144735741 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289840881 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (14510471 / 50000000 : ℝ)
  | ⟨38,_⟩ => (58115419 / 200000000 : ℝ)
  | ⟨39,_⟩ => (290943397 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291308841 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291673433 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292037173 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12305Cell0 :
    0 ≤ cap12305 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨0,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12305 ⟨0,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨0,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell1 :
    0 ≤ cap12305 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨1,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12305 ⟨1,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨1,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell2 :
    0 ≤ cap12305 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨2,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12305 ⟨2,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨2,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell3 :
    0 ≤ cap12305 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨3,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12305 ⟨3,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨3,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell4 :
    0 ≤ cap12305 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨4,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12305 ⟨4,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨4,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell5 :
    0 ≤ cap12305 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨5,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12305 ⟨5,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨5,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell6 :
    0 ≤ cap12305 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨6,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12305 ⟨6,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨6,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell7 :
    0 ≤ cap12305 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨7,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12305 ⟨7,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨7,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell8 :
    0 ≤ cap12305 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨8,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12305 ⟨8,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨8,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell9 :
    0 ≤ cap12305 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨9,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12305 ⟨9,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨9,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell10 :
    0 ≤ cap12305 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨10,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12305 ⟨10,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨10,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell11 :
    0 ≤ cap12305 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨11,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12305 ⟨11,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨11,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell12 :
    0 ≤ cap12305 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨12,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12305 ⟨12,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨12,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell13 :
    0 ≤ cap12305 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨13,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12305 ⟨13,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨13,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell14 :
    0 ≤ cap12305 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨14,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12305 ⟨14,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨14,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell15 :
    0 ≤ cap12305 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨15,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12305 ⟨15,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨15,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell16 :
    0 ≤ cap12305 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨16,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12305 ⟨16,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨16,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell17 :
    0 ≤ cap12305 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨17,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12305 ⟨17,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨17,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell18 :
    0 ≤ cap12305 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨18,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12305 ⟨18,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨18,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell19 :
    0 ≤ cap12305 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨19,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12305 ⟨19,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨19,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell20 :
    0 ≤ cap12305 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨20,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12305 ⟨20,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨20,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell21 :
    0 ≤ cap12305 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨21,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12305 ⟨21,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨21,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell22 :
    0 ≤ cap12305 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨22,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12305 ⟨22,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨22,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell23 :
    0 ≤ cap12305 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨23,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12305 ⟨23,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨23,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell24 :
    0 ≤ cap12305 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨24,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12305 ⟨24,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨24,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell25 :
    0 ≤ cap12305 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨25,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12305 ⟨25,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨25,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell26 :
    0 ≤ cap12305 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨26,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12305 ⟨26,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨26,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell27 :
    0 ≤ cap12305 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨27,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12305 ⟨27,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨27,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell28 :
    0 ≤ cap12305 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨28,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12305 ⟨28,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨28,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell29 :
    0 ≤ cap12305 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨29,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12305 ⟨29,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨29,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell30 :
    0 ≤ cap12305 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨30,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12305 ⟨30,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨30,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell31 :
    0 ≤ cap12305 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨31,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12305 ⟨31,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨31,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell32 :
    0 ≤ cap12305 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨32,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12305 ⟨32,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨32,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell33 :
    0 ≤ cap12305 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨33,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12305 ⟨33,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨33,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell34 :
    0 ≤ cap12305 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨34,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12305 ⟨34,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨34,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell35 :
    0 ≤ cap12305 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨35,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12305 ⟨35,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨35,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell36 :
    0 ≤ cap12305 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨36,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12305 ⟨36,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨36,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell37 :
    0 ≤ cap12305 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨37,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12305 ⟨37,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨37,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell38 :
    0 ≤ cap12305 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨38,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12305 ⟨38,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨38,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell39 :
    0 ≤ cap12305 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨39,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12305 ⟨39,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨39,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell40 :
    0 ≤ cap12305 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨40,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12305 ⟨40,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨40,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell41 :
    0 ≤ cap12305 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨41,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12305 ⟨41,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨41,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cell42 :
    0 ≤ cap12305 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12305 (parameters ⟨42,by decide⟩)
      (scalarRow12305.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12305 ⟨42,by decide⟩ ∧
    (scalarRow12305.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 ⟨42,by decide⟩ + (scalarRow12305.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12305.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12305.targetFrame := by
  norm_num [cap12305, scalarRow12305, sourceIndex, cell12305, BstLean.Part263.envelope, parameters]

theorem repair12305Cells (j : Fin 43) :
    0 ≤ cap12305 j ∧
    BstLean.Part263.envelope 12305 (parameters j) (scalarRow12305.table (sourceIndex j)).upper ≤ cap12305 j ∧
    (scalarRow12305.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12305 j + (scalarRow12305.table (sourceIndex j)).centre) /
      (scalarRow12305.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12305.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12305Cell0
  | ⟨1,_⟩ => exact repair12305Cell1
  | ⟨2,_⟩ => exact repair12305Cell2
  | ⟨3,_⟩ => exact repair12305Cell3
  | ⟨4,_⟩ => exact repair12305Cell4
  | ⟨5,_⟩ => exact repair12305Cell5
  | ⟨6,_⟩ => exact repair12305Cell6
  | ⟨7,_⟩ => exact repair12305Cell7
  | ⟨8,_⟩ => exact repair12305Cell8
  | ⟨9,_⟩ => exact repair12305Cell9
  | ⟨10,_⟩ => exact repair12305Cell10
  | ⟨11,_⟩ => exact repair12305Cell11
  | ⟨12,_⟩ => exact repair12305Cell12
  | ⟨13,_⟩ => exact repair12305Cell13
  | ⟨14,_⟩ => exact repair12305Cell14
  | ⟨15,_⟩ => exact repair12305Cell15
  | ⟨16,_⟩ => exact repair12305Cell16
  | ⟨17,_⟩ => exact repair12305Cell17
  | ⟨18,_⟩ => exact repair12305Cell18
  | ⟨19,_⟩ => exact repair12305Cell19
  | ⟨20,_⟩ => exact repair12305Cell20
  | ⟨21,_⟩ => exact repair12305Cell21
  | ⟨22,_⟩ => exact repair12305Cell22
  | ⟨23,_⟩ => exact repair12305Cell23
  | ⟨24,_⟩ => exact repair12305Cell24
  | ⟨25,_⟩ => exact repair12305Cell25
  | ⟨26,_⟩ => exact repair12305Cell26
  | ⟨27,_⟩ => exact repair12305Cell27
  | ⟨28,_⟩ => exact repair12305Cell28
  | ⟨29,_⟩ => exact repair12305Cell29
  | ⟨30,_⟩ => exact repair12305Cell30
  | ⟨31,_⟩ => exact repair12305Cell31
  | ⟨32,_⟩ => exact repair12305Cell32
  | ⟨33,_⟩ => exact repair12305Cell33
  | ⟨34,_⟩ => exact repair12305Cell34
  | ⟨35,_⟩ => exact repair12305Cell35
  | ⟨36,_⟩ => exact repair12305Cell36
  | ⟨37,_⟩ => exact repair12305Cell37
  | ⟨38,_⟩ => exact repair12305Cell38
  | ⟨39,_⟩ => exact repair12305Cell39
  | ⟨40,_⟩ => exact repair12305Cell40
  | ⟨41,_⟩ => exact repair12305Cell41
  | ⟨42,_⟩ => exact repair12305Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12305 : FrameRepair 12305 scalarRow12305 where
  cap := cap12305
  cap_nonneg := fun j => (repair12305Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12305])
  endpoint := fun j => (repair12305Cells j).2.1
  endpoint_upper := fun j => (repair12305Cells j).2.2.1
  frame := fun j => (repair12305Cells j).2.2.2

noncomputable def cap12306 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55189321 / 200000000 : ℝ)
  | ⟨1,_⟩ => (276349351 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276751103 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138575929 / 500000000 : ℝ)
  | ⟨4,_⟩ => (138775811 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277950397 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278347711 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (6968613 / 25000000 : ℝ)
  | ⟨8,_⟩ => (545196 / 1953125 : ℝ)
  | ⟨9,_⟩ => (279535213 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279929103 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56064309 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280713509 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140552013 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281494477 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70470957 / 250000000 : ℝ)
  | ⟨16,_⟩ => (70568059 / 250000000 : ℝ)
  | ⟨17,_⟩ => (141329857 / 500000000 : ℝ)
  | ⟨18,_⟩ => (70761563 / 250000000 : ℝ)
  | ⟨19,_⟩ => (141715931 / 500000000 : ℝ)
  | ⟨20,_⟩ => (56763309 / 200000000 : ℝ)
  | ⟨21,_⟩ => (35525039 / 125000000 : ℝ)
  | ⟨22,_⟩ => (56916631 / 200000000 : ℝ)
  | ⟨23,_⟩ => (71241147 / 250000000 : ℝ)
  | ⟨24,_⟩ => (35668201 / 125000000 : ℝ)
  | ⟨25,_⟩ => (285725267 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143052261 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286482377 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286859337 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287235401 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287610071 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287984357 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288357763 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288729779 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289100919 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289471189 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289840581 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (58041823 / 200000000 : ℝ)
  | ⟨38,_⟩ => (290576783 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (7273577 / 25000000 : ℝ)
  | ⟨40,_⟩ => (291308517 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (18229569 / 62500000 : ℝ)
  | ⟨42,_⟩ => (146018419 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12306Cell0 :
    0 ≤ cap12306 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨0,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12306 ⟨0,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨0,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell1 :
    0 ≤ cap12306 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨1,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12306 ⟨1,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨1,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell2 :
    0 ≤ cap12306 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨2,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12306 ⟨2,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨2,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell3 :
    0 ≤ cap12306 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨3,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12306 ⟨3,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨3,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell4 :
    0 ≤ cap12306 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨4,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12306 ⟨4,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨4,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell5 :
    0 ≤ cap12306 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨5,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12306 ⟨5,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨5,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell6 :
    0 ≤ cap12306 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨6,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12306 ⟨6,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨6,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell7 :
    0 ≤ cap12306 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨7,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12306 ⟨7,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨7,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell8 :
    0 ≤ cap12306 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨8,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12306 ⟨8,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨8,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell9 :
    0 ≤ cap12306 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨9,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12306 ⟨9,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨9,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell10 :
    0 ≤ cap12306 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨10,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12306 ⟨10,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨10,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell11 :
    0 ≤ cap12306 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨11,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12306 ⟨11,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨11,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell12 :
    0 ≤ cap12306 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨12,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12306 ⟨12,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨12,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell13 :
    0 ≤ cap12306 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨13,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12306 ⟨13,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨13,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell14 :
    0 ≤ cap12306 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨14,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12306 ⟨14,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨14,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell15 :
    0 ≤ cap12306 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨15,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12306 ⟨15,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨15,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell16 :
    0 ≤ cap12306 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨16,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12306 ⟨16,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨16,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell17 :
    0 ≤ cap12306 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨17,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12306 ⟨17,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨17,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell18 :
    0 ≤ cap12306 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨18,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12306 ⟨18,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨18,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell19 :
    0 ≤ cap12306 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨19,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12306 ⟨19,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨19,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell20 :
    0 ≤ cap12306 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨20,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12306 ⟨20,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨20,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell21 :
    0 ≤ cap12306 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨21,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12306 ⟨21,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨21,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell22 :
    0 ≤ cap12306 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨22,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12306 ⟨22,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨22,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell23 :
    0 ≤ cap12306 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨23,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12306 ⟨23,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨23,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell24 :
    0 ≤ cap12306 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨24,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12306 ⟨24,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨24,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell25 :
    0 ≤ cap12306 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨25,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12306 ⟨25,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨25,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell26 :
    0 ≤ cap12306 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨26,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12306 ⟨26,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨26,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell27 :
    0 ≤ cap12306 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨27,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12306 ⟨27,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨27,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell28 :
    0 ≤ cap12306 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨28,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12306 ⟨28,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨28,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell29 :
    0 ≤ cap12306 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨29,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12306 ⟨29,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨29,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell30 :
    0 ≤ cap12306 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨30,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12306 ⟨30,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨30,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell31 :
    0 ≤ cap12306 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨31,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12306 ⟨31,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨31,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell32 :
    0 ≤ cap12306 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨32,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12306 ⟨32,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨32,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell33 :
    0 ≤ cap12306 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨33,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12306 ⟨33,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨33,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell34 :
    0 ≤ cap12306 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨34,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12306 ⟨34,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨34,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell35 :
    0 ≤ cap12306 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨35,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12306 ⟨35,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨35,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell36 :
    0 ≤ cap12306 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨36,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12306 ⟨36,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨36,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell37 :
    0 ≤ cap12306 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨37,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12306 ⟨37,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨37,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell38 :
    0 ≤ cap12306 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨38,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12306 ⟨38,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨38,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell39 :
    0 ≤ cap12306 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨39,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12306 ⟨39,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨39,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell40 :
    0 ≤ cap12306 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨40,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12306 ⟨40,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨40,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell41 :
    0 ≤ cap12306 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨41,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12306 ⟨41,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨41,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cell42 :
    0 ≤ cap12306 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12306 (parameters ⟨42,by decide⟩)
      (scalarRow12306.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12306 ⟨42,by decide⟩ ∧
    (scalarRow12306.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 ⟨42,by decide⟩ + (scalarRow12306.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12306.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12306.targetFrame := by
  norm_num [cap12306, scalarRow12306, sourceIndex, cell12306, BstLean.Part263.envelope, parameters]

theorem repair12306Cells (j : Fin 43) :
    0 ≤ cap12306 j ∧
    BstLean.Part263.envelope 12306 (parameters j) (scalarRow12306.table (sourceIndex j)).upper ≤ cap12306 j ∧
    (scalarRow12306.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12306 j + (scalarRow12306.table (sourceIndex j)).centre) /
      (scalarRow12306.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12306.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12306Cell0
  | ⟨1,_⟩ => exact repair12306Cell1
  | ⟨2,_⟩ => exact repair12306Cell2
  | ⟨3,_⟩ => exact repair12306Cell3
  | ⟨4,_⟩ => exact repair12306Cell4
  | ⟨5,_⟩ => exact repair12306Cell5
  | ⟨6,_⟩ => exact repair12306Cell6
  | ⟨7,_⟩ => exact repair12306Cell7
  | ⟨8,_⟩ => exact repair12306Cell8
  | ⟨9,_⟩ => exact repair12306Cell9
  | ⟨10,_⟩ => exact repair12306Cell10
  | ⟨11,_⟩ => exact repair12306Cell11
  | ⟨12,_⟩ => exact repair12306Cell12
  | ⟨13,_⟩ => exact repair12306Cell13
  | ⟨14,_⟩ => exact repair12306Cell14
  | ⟨15,_⟩ => exact repair12306Cell15
  | ⟨16,_⟩ => exact repair12306Cell16
  | ⟨17,_⟩ => exact repair12306Cell17
  | ⟨18,_⟩ => exact repair12306Cell18
  | ⟨19,_⟩ => exact repair12306Cell19
  | ⟨20,_⟩ => exact repair12306Cell20
  | ⟨21,_⟩ => exact repair12306Cell21
  | ⟨22,_⟩ => exact repair12306Cell22
  | ⟨23,_⟩ => exact repair12306Cell23
  | ⟨24,_⟩ => exact repair12306Cell24
  | ⟨25,_⟩ => exact repair12306Cell25
  | ⟨26,_⟩ => exact repair12306Cell26
  | ⟨27,_⟩ => exact repair12306Cell27
  | ⟨28,_⟩ => exact repair12306Cell28
  | ⟨29,_⟩ => exact repair12306Cell29
  | ⟨30,_⟩ => exact repair12306Cell30
  | ⟨31,_⟩ => exact repair12306Cell31
  | ⟨32,_⟩ => exact repair12306Cell32
  | ⟨33,_⟩ => exact repair12306Cell33
  | ⟨34,_⟩ => exact repair12306Cell34
  | ⟨35,_⟩ => exact repair12306Cell35
  | ⟨36,_⟩ => exact repair12306Cell36
  | ⟨37,_⟩ => exact repair12306Cell37
  | ⟨38,_⟩ => exact repair12306Cell38
  | ⟨39,_⟩ => exact repair12306Cell39
  | ⟨40,_⟩ => exact repair12306Cell40
  | ⟨41,_⟩ => exact repair12306Cell41
  | ⟨42,_⟩ => exact repair12306Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12306 : FrameRepair 12306 scalarRow12306 where
  cap := cap12306
  cap_nonneg := fun j => (repair12306Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12306])
  endpoint := fun j => (repair12306Cells j).2.1
  endpoint_upper := fun j => (repair12306Cells j).2.2.1
  frame := fun j => (repair12306Cells j).2.2.2

noncomputable def cap12307 : Fin 43 → ℝ
  | ⟨0,_⟩ => (27594653 / 100000000 : ℝ)
  | ⟨1,_⟩ => (27634927 / 100000000 : ℝ)
  | ⟨2,_⟩ => (55350203 / 200000000 : ℝ)
  | ⟨3,_⟩ => (277151763 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277551521 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (27795029 / 100000000 : ℝ)
  | ⟨6,_⟩ => (139173799 / 500000000 : ℝ)
  | ⟨7,_⟩ => (696861 / 2500000 : ℝ)
  | ⟨8,_⟩ => (139570113 / 500000000 : ℝ)
  | ⟨9,_⟩ => (6988377 / 25000000 : ℝ)
  | ⟨10,_⟩ => (69982241 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280321399 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280713357 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70275967 / 250000000 : ℝ)
  | ⟨14,_⟩ => (35186789 / 125000000 : ℝ)
  | ⟨15,_⟩ => (281883657 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282272059 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282659531 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283046063 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141715833 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283816343 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (35525013 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284582941 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284964367 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285345381 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142862517 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286104283 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71620533 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143429543 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287235143 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (17975613 / 62500000 : ℝ)
  | ⟨31,_⟩ => (35998011 / 125000000 : ℝ)
  | ⟨32,_⟩ => (18022343 / 62500000 : ℝ)
  | ⟨33,_⟩ => (288729497 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (36137579 / 125000000 : ℝ)
  | ⟨35,_⟩ => (57894179 / 200000000 : ℝ)
  | ⟨36,_⟩ => (144920141 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290208809 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (36322059 / 125000000 : ℝ)
  | ⟨39,_⟩ => (145471381 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145654097 / 500000000 : ℝ)
  | ⟨41,_⟩ => (145836387 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292036503 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12307Cell0 :
    0 ≤ cap12307 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨0,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12307 ⟨0,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨0,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell1 :
    0 ≤ cap12307 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨1,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12307 ⟨1,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨1,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell2 :
    0 ≤ cap12307 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨2,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12307 ⟨2,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨2,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell3 :
    0 ≤ cap12307 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨3,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12307 ⟨3,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨3,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell4 :
    0 ≤ cap12307 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨4,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12307 ⟨4,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨4,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell5 :
    0 ≤ cap12307 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨5,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12307 ⟨5,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨5,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell6 :
    0 ≤ cap12307 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨6,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12307 ⟨6,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨6,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell7 :
    0 ≤ cap12307 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨7,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12307 ⟨7,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨7,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell8 :
    0 ≤ cap12307 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨8,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12307 ⟨8,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨8,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell9 :
    0 ≤ cap12307 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨9,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12307 ⟨9,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨9,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell10 :
    0 ≤ cap12307 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨10,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12307 ⟨10,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨10,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell11 :
    0 ≤ cap12307 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨11,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12307 ⟨11,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨11,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell12 :
    0 ≤ cap12307 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨12,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12307 ⟨12,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨12,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell13 :
    0 ≤ cap12307 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨13,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12307 ⟨13,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨13,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell14 :
    0 ≤ cap12307 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨14,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12307 ⟨14,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨14,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell15 :
    0 ≤ cap12307 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨15,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12307 ⟨15,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨15,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell16 :
    0 ≤ cap12307 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨16,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12307 ⟨16,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨16,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell17 :
    0 ≤ cap12307 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨17,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12307 ⟨17,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨17,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell18 :
    0 ≤ cap12307 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨18,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12307 ⟨18,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨18,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell19 :
    0 ≤ cap12307 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨19,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12307 ⟨19,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨19,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell20 :
    0 ≤ cap12307 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨20,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12307 ⟨20,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨20,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell21 :
    0 ≤ cap12307 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨21,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12307 ⟨21,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨21,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell22 :
    0 ≤ cap12307 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨22,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12307 ⟨22,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨22,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell23 :
    0 ≤ cap12307 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨23,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12307 ⟨23,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨23,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell24 :
    0 ≤ cap12307 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨24,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12307 ⟨24,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨24,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell25 :
    0 ≤ cap12307 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨25,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12307 ⟨25,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨25,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell26 :
    0 ≤ cap12307 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨26,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12307 ⟨26,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨26,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell27 :
    0 ≤ cap12307 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨27,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12307 ⟨27,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨27,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell28 :
    0 ≤ cap12307 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨28,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12307 ⟨28,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨28,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell29 :
    0 ≤ cap12307 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨29,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12307 ⟨29,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨29,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell30 :
    0 ≤ cap12307 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨30,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12307 ⟨30,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨30,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell31 :
    0 ≤ cap12307 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨31,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12307 ⟨31,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨31,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell32 :
    0 ≤ cap12307 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨32,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12307 ⟨32,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨32,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell33 :
    0 ≤ cap12307 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨33,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12307 ⟨33,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨33,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell34 :
    0 ≤ cap12307 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨34,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12307 ⟨34,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨34,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell35 :
    0 ≤ cap12307 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨35,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12307 ⟨35,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨35,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell36 :
    0 ≤ cap12307 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨36,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12307 ⟨36,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨36,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell37 :
    0 ≤ cap12307 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨37,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12307 ⟨37,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨37,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell38 :
    0 ≤ cap12307 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨38,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12307 ⟨38,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨38,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell39 :
    0 ≤ cap12307 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨39,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12307 ⟨39,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨39,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell40 :
    0 ≤ cap12307 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨40,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12307 ⟨40,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨40,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell41 :
    0 ≤ cap12307 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨41,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12307 ⟨41,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨41,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cell42 :
    0 ≤ cap12307 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12307 (parameters ⟨42,by decide⟩)
      (scalarRow12307.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12307 ⟨42,by decide⟩ ∧
    (scalarRow12307.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 ⟨42,by decide⟩ + (scalarRow12307.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12307.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12307.targetFrame := by
  norm_num [cap12307, scalarRow12307, sourceIndex, cell12307, BstLean.Part263.envelope, parameters]

theorem repair12307Cells (j : Fin 43) :
    0 ≤ cap12307 j ∧
    BstLean.Part263.envelope 12307 (parameters j) (scalarRow12307.table (sourceIndex j)).upper ≤ cap12307 j ∧
    (scalarRow12307.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12307 j + (scalarRow12307.table (sourceIndex j)).centre) /
      (scalarRow12307.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12307.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12307Cell0
  | ⟨1,_⟩ => exact repair12307Cell1
  | ⟨2,_⟩ => exact repair12307Cell2
  | ⟨3,_⟩ => exact repair12307Cell3
  | ⟨4,_⟩ => exact repair12307Cell4
  | ⟨5,_⟩ => exact repair12307Cell5
  | ⟨6,_⟩ => exact repair12307Cell6
  | ⟨7,_⟩ => exact repair12307Cell7
  | ⟨8,_⟩ => exact repair12307Cell8
  | ⟨9,_⟩ => exact repair12307Cell9
  | ⟨10,_⟩ => exact repair12307Cell10
  | ⟨11,_⟩ => exact repair12307Cell11
  | ⟨12,_⟩ => exact repair12307Cell12
  | ⟨13,_⟩ => exact repair12307Cell13
  | ⟨14,_⟩ => exact repair12307Cell14
  | ⟨15,_⟩ => exact repair12307Cell15
  | ⟨16,_⟩ => exact repair12307Cell16
  | ⟨17,_⟩ => exact repair12307Cell17
  | ⟨18,_⟩ => exact repair12307Cell18
  | ⟨19,_⟩ => exact repair12307Cell19
  | ⟨20,_⟩ => exact repair12307Cell20
  | ⟨21,_⟩ => exact repair12307Cell21
  | ⟨22,_⟩ => exact repair12307Cell22
  | ⟨23,_⟩ => exact repair12307Cell23
  | ⟨24,_⟩ => exact repair12307Cell24
  | ⟨25,_⟩ => exact repair12307Cell25
  | ⟨26,_⟩ => exact repair12307Cell26
  | ⟨27,_⟩ => exact repair12307Cell27
  | ⟨28,_⟩ => exact repair12307Cell28
  | ⟨29,_⟩ => exact repair12307Cell29
  | ⟨30,_⟩ => exact repair12307Cell30
  | ⟨31,_⟩ => exact repair12307Cell31
  | ⟨32,_⟩ => exact repair12307Cell32
  | ⟨33,_⟩ => exact repair12307Cell33
  | ⟨34,_⟩ => exact repair12307Cell34
  | ⟨35,_⟩ => exact repair12307Cell35
  | ⟨36,_⟩ => exact repair12307Cell36
  | ⟨37,_⟩ => exact repair12307Cell37
  | ⟨38,_⟩ => exact repair12307Cell38
  | ⟨39,_⟩ => exact repair12307Cell39
  | ⟨40,_⟩ => exact repair12307Cell40
  | ⟨41,_⟩ => exact repair12307Cell41
  | ⟨42,_⟩ => exact repair12307Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12307 : FrameRepair 12307 scalarRow12307 where
  cap := cap12307
  cap_nonneg := fun j => (repair12307Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12307])
  endpoint := fun j => (repair12307Cells j).2.1
  endpoint_upper := fun j => (repair12307Cells j).2.2.1
  frame := fun j => (repair12307Cells j).2.2.2

noncomputable def cap12308 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55189291 / 200000000 : ℝ)
  | ⟨1,_⟩ => (69087297 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276750927 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277151669 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (13877571 / 50000000 : ℝ)
  | ⟨5,_⟩ => (138975091 / 500000000 : ℝ)
  | ⟨6,_⟩ => (69586871 / 250000000 : ℝ)
  | ⟨7,_⟩ => (278744279 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279140099 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279534947 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (34991103 / 125000000 : ℝ)
  | ⟨11,_⟩ => (280321253 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (56142641 / 200000000 : ℝ)
  | ⟨13,_⟩ => (28110371 / 100000000 : ℝ)
  | ⟨14,_⟩ => (70373537 / 250000000 : ℝ)
  | ⟨15,_⟩ => (140941743 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141135941 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282659347 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283045873 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283431471 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283816141 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (35524987 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284582727 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284964147 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142672577 / 500000000 : ℝ)
  | ⟨25,_⟩ => (285724801 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (71526011 / 250000000 : ℝ)
  | ⟨27,_⟩ => (286481887 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143429417 / 500000000 : ℝ)
  | ⟨29,_⟩ => (143617443 / 500000000 : ℝ)
  | ⟨30,_⟩ => (35951193 / 125000000 : ℝ)
  | ⟨31,_⟩ => (287983819 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72089303 / 250000000 : ℝ)
  | ⟨33,_⟩ => (2255697 / 7812500 : ℝ)
  | ⟨34,_⟩ => (36137543 / 125000000 : ℝ)
  | ⟨35,_⟩ => (144735301 / 500000000 : ℝ)
  | ⟨36,_⟩ => (144919991 / 500000000 : ℝ)
  | ⟨37,_⟩ => (36276063 / 125000000 : ℝ)
  | ⟨38,_⟩ => (290576161 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (58188489 / 200000000 : ℝ)
  | ⟨40,_⟩ => (291307871 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (58334489 / 200000000 : ℝ)
  | ⟨42,_⟩ => (36504521 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12308Cell0 :
    0 ≤ cap12308 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨0,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12308 ⟨0,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨0,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell1 :
    0 ≤ cap12308 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨1,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12308 ⟨1,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨1,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell2 :
    0 ≤ cap12308 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨2,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12308 ⟨2,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨2,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell3 :
    0 ≤ cap12308 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨3,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12308 ⟨3,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨3,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell4 :
    0 ≤ cap12308 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨4,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12308 ⟨4,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨4,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell5 :
    0 ≤ cap12308 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨5,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12308 ⟨5,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨5,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell6 :
    0 ≤ cap12308 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨6,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12308 ⟨6,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨6,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell7 :
    0 ≤ cap12308 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨7,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12308 ⟨7,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨7,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell8 :
    0 ≤ cap12308 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨8,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12308 ⟨8,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨8,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell9 :
    0 ≤ cap12308 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨9,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12308 ⟨9,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨9,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell10 :
    0 ≤ cap12308 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨10,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12308 ⟨10,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨10,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell11 :
    0 ≤ cap12308 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨11,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12308 ⟨11,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨11,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell12 :
    0 ≤ cap12308 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨12,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12308 ⟨12,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨12,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell13 :
    0 ≤ cap12308 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨13,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12308 ⟨13,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨13,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell14 :
    0 ≤ cap12308 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨14,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12308 ⟨14,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨14,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell15 :
    0 ≤ cap12308 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨15,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12308 ⟨15,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨15,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell16 :
    0 ≤ cap12308 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨16,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12308 ⟨16,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨16,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell17 :
    0 ≤ cap12308 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨17,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12308 ⟨17,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨17,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell18 :
    0 ≤ cap12308 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨18,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12308 ⟨18,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨18,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell19 :
    0 ≤ cap12308 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨19,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12308 ⟨19,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨19,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell20 :
    0 ≤ cap12308 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨20,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12308 ⟨20,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨20,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell21 :
    0 ≤ cap12308 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨21,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12308 ⟨21,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨21,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell22 :
    0 ≤ cap12308 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨22,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12308 ⟨22,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨22,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell23 :
    0 ≤ cap12308 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨23,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12308 ⟨23,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨23,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell24 :
    0 ≤ cap12308 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨24,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12308 ⟨24,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨24,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell25 :
    0 ≤ cap12308 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨25,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12308 ⟨25,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨25,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell26 :
    0 ≤ cap12308 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨26,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12308 ⟨26,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨26,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell27 :
    0 ≤ cap12308 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨27,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12308 ⟨27,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨27,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell28 :
    0 ≤ cap12308 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨28,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12308 ⟨28,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨28,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell29 :
    0 ≤ cap12308 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨29,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12308 ⟨29,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨29,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell30 :
    0 ≤ cap12308 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨30,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12308 ⟨30,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨30,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell31 :
    0 ≤ cap12308 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨31,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12308 ⟨31,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨31,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell32 :
    0 ≤ cap12308 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨32,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12308 ⟨32,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨32,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell33 :
    0 ≤ cap12308 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨33,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12308 ⟨33,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨33,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell34 :
    0 ≤ cap12308 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨34,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12308 ⟨34,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨34,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell35 :
    0 ≤ cap12308 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨35,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12308 ⟨35,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨35,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell36 :
    0 ≤ cap12308 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨36,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12308 ⟨36,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨36,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell37 :
    0 ≤ cap12308 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨37,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12308 ⟨37,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨37,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell38 :
    0 ≤ cap12308 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨38,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12308 ⟨38,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨38,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell39 :
    0 ≤ cap12308 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨39,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12308 ⟨39,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨39,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell40 :
    0 ≤ cap12308 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨40,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12308 ⟨40,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨40,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell41 :
    0 ≤ cap12308 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨41,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12308 ⟨41,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨41,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cell42 :
    0 ≤ cap12308 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12308 (parameters ⟨42,by decide⟩)
      (scalarRow12308.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12308 ⟨42,by decide⟩ ∧
    (scalarRow12308.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 ⟨42,by decide⟩ + (scalarRow12308.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12308.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12308.targetFrame := by
  norm_num [cap12308, scalarRow12308, sourceIndex, cell12308, BstLean.Part263.envelope, parameters]

theorem repair12308Cells (j : Fin 43) :
    0 ≤ cap12308 j ∧
    BstLean.Part263.envelope 12308 (parameters j) (scalarRow12308.table (sourceIndex j)).upper ≤ cap12308 j ∧
    (scalarRow12308.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12308 j + (scalarRow12308.table (sourceIndex j)).centre) /
      (scalarRow12308.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12308.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12308Cell0
  | ⟨1,_⟩ => exact repair12308Cell1
  | ⟨2,_⟩ => exact repair12308Cell2
  | ⟨3,_⟩ => exact repair12308Cell3
  | ⟨4,_⟩ => exact repair12308Cell4
  | ⟨5,_⟩ => exact repair12308Cell5
  | ⟨6,_⟩ => exact repair12308Cell6
  | ⟨7,_⟩ => exact repair12308Cell7
  | ⟨8,_⟩ => exact repair12308Cell8
  | ⟨9,_⟩ => exact repair12308Cell9
  | ⟨10,_⟩ => exact repair12308Cell10
  | ⟨11,_⟩ => exact repair12308Cell11
  | ⟨12,_⟩ => exact repair12308Cell12
  | ⟨13,_⟩ => exact repair12308Cell13
  | ⟨14,_⟩ => exact repair12308Cell14
  | ⟨15,_⟩ => exact repair12308Cell15
  | ⟨16,_⟩ => exact repair12308Cell16
  | ⟨17,_⟩ => exact repair12308Cell17
  | ⟨18,_⟩ => exact repair12308Cell18
  | ⟨19,_⟩ => exact repair12308Cell19
  | ⟨20,_⟩ => exact repair12308Cell20
  | ⟨21,_⟩ => exact repair12308Cell21
  | ⟨22,_⟩ => exact repair12308Cell22
  | ⟨23,_⟩ => exact repair12308Cell23
  | ⟨24,_⟩ => exact repair12308Cell24
  | ⟨25,_⟩ => exact repair12308Cell25
  | ⟨26,_⟩ => exact repair12308Cell26
  | ⟨27,_⟩ => exact repair12308Cell27
  | ⟨28,_⟩ => exact repair12308Cell28
  | ⟨29,_⟩ => exact repair12308Cell29
  | ⟨30,_⟩ => exact repair12308Cell30
  | ⟨31,_⟩ => exact repair12308Cell31
  | ⟨32,_⟩ => exact repair12308Cell32
  | ⟨33,_⟩ => exact repair12308Cell33
  | ⟨34,_⟩ => exact repair12308Cell34
  | ⟨35,_⟩ => exact repair12308Cell35
  | ⟨36,_⟩ => exact repair12308Cell36
  | ⟨37,_⟩ => exact repair12308Cell37
  | ⟨38,_⟩ => exact repair12308Cell38
  | ⟨39,_⟩ => exact repair12308Cell39
  | ⟨40,_⟩ => exact repair12308Cell40
  | ⟨41,_⟩ => exact repair12308Cell41
  | ⟨42,_⟩ => exact repair12308Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12308 : FrameRepair 12308 scalarRow12308 where
  cap := cap12308
  cap_nonneg := fun j => (repair12308Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12308])
  endpoint := fun j => (repair12308Cells j).2.1
  endpoint_upper := fun j => (repair12308Cells j).2.2.1
  frame := fun j => (repair12308Cells j).2.2.2

noncomputable def cap12309 : Fin 43 → ℝ
  | ⟨0,_⟩ => (13797319 / 50000000 : ℝ)
  | ⟨1,_⟩ => (138174553 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276750839 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138575787 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277551319 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (11118003 / 40000000 : ℝ)
  | ⟨6,_⟩ => (27834737 / 100000000 : ℝ)
  | ⟨7,_⟩ => (278744159 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279139973 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139767407 / 500000000 : ℝ)
  | ⟨10,_⟩ => (55985737 / 200000000 : ℝ)
  | ⟨11,_⟩ => (70080277 / 250000000 : ℝ)
  | ⟨12,_⟩ => (280713053 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (4392243 / 15625000 : ℝ)
  | ⟨14,_⟩ => (8796687 / 31250000 : ℝ)
  | ⟨15,_⟩ => (70470829 / 250000000 : ℝ)
  | ⟨16,_⟩ => (56454341 / 200000000 : ℝ)
  | ⟨17,_⟩ => (70664791 / 250000000 : ℝ)
  | ⟨18,_⟩ => (70761421 / 250000000 : ℝ)
  | ⟨19,_⟩ => (11337251 / 40000000 : ℝ)
  | ⟨20,_⟩ => (283815939 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (35524961 / 125000000 : ℝ)
  | ⟨22,_⟩ => (17786407 / 62500000 : ℝ)
  | ⟨23,_⟩ => (142481963 / 500000000 : ℝ)
  | ⟨24,_⟩ => (8917029 / 31250000 : ℝ)
  | ⟨25,_⟩ => (285724569 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (57220761 / 200000000 : ℝ)
  | ⟨27,_⟩ => (143240821 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286858583 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287234629 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287609281 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287983549 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288356937 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144364467 / 500000000 : ℝ)
  | ⟨34,_⟩ => (289100057 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72367577 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289839683 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145104099 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290575849 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (18183883 / 62500000 : ℝ)
  | ⟨40,_⟩ => (291307547 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (72918029 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292035833 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12309Cell0 :
    0 ≤ cap12309 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨0,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12309 ⟨0,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨0,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell1 :
    0 ≤ cap12309 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨1,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12309 ⟨1,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨1,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell2 :
    0 ≤ cap12309 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨2,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12309 ⟨2,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨2,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell3 :
    0 ≤ cap12309 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨3,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12309 ⟨3,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨3,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell4 :
    0 ≤ cap12309 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨4,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12309 ⟨4,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨4,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell5 :
    0 ≤ cap12309 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨5,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12309 ⟨5,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨5,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell6 :
    0 ≤ cap12309 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨6,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12309 ⟨6,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨6,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell7 :
    0 ≤ cap12309 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨7,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12309 ⟨7,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨7,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell8 :
    0 ≤ cap12309 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨8,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12309 ⟨8,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨8,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell9 :
    0 ≤ cap12309 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨9,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12309 ⟨9,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨9,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell10 :
    0 ≤ cap12309 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨10,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12309 ⟨10,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨10,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell11 :
    0 ≤ cap12309 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨11,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12309 ⟨11,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨11,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell12 :
    0 ≤ cap12309 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨12,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12309 ⟨12,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨12,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell13 :
    0 ≤ cap12309 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨13,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12309 ⟨13,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨13,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell14 :
    0 ≤ cap12309 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨14,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12309 ⟨14,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨14,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell15 :
    0 ≤ cap12309 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨15,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12309 ⟨15,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨15,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell16 :
    0 ≤ cap12309 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨16,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12309 ⟨16,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨16,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell17 :
    0 ≤ cap12309 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨17,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12309 ⟨17,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨17,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell18 :
    0 ≤ cap12309 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨18,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12309 ⟨18,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨18,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell19 :
    0 ≤ cap12309 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨19,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12309 ⟨19,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨19,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell20 :
    0 ≤ cap12309 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨20,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12309 ⟨20,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨20,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell21 :
    0 ≤ cap12309 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨21,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12309 ⟨21,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨21,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell22 :
    0 ≤ cap12309 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨22,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12309 ⟨22,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨22,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell23 :
    0 ≤ cap12309 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨23,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12309 ⟨23,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨23,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell24 :
    0 ≤ cap12309 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨24,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12309 ⟨24,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨24,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell25 :
    0 ≤ cap12309 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨25,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12309 ⟨25,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨25,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell26 :
    0 ≤ cap12309 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨26,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12309 ⟨26,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨26,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell27 :
    0 ≤ cap12309 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨27,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12309 ⟨27,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨27,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell28 :
    0 ≤ cap12309 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨28,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12309 ⟨28,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨28,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell29 :
    0 ≤ cap12309 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨29,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12309 ⟨29,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨29,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell30 :
    0 ≤ cap12309 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨30,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12309 ⟨30,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨30,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell31 :
    0 ≤ cap12309 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨31,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12309 ⟨31,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨31,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell32 :
    0 ≤ cap12309 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨32,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12309 ⟨32,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨32,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell33 :
    0 ≤ cap12309 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨33,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12309 ⟨33,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨33,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell34 :
    0 ≤ cap12309 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨34,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12309 ⟨34,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨34,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell35 :
    0 ≤ cap12309 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨35,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12309 ⟨35,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨35,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell36 :
    0 ≤ cap12309 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨36,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12309 ⟨36,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨36,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell37 :
    0 ≤ cap12309 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨37,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12309 ⟨37,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨37,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell38 :
    0 ≤ cap12309 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨38,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12309 ⟨38,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨38,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell39 :
    0 ≤ cap12309 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨39,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12309 ⟨39,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨39,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell40 :
    0 ≤ cap12309 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨40,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12309 ⟨40,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨40,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell41 :
    0 ≤ cap12309 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨41,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12309 ⟨41,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨41,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cell42 :
    0 ≤ cap12309 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12309 (parameters ⟨42,by decide⟩)
      (scalarRow12309.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12309 ⟨42,by decide⟩ ∧
    (scalarRow12309.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 ⟨42,by decide⟩ + (scalarRow12309.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12309.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12309.targetFrame := by
  norm_num [cap12309, scalarRow12309, sourceIndex, cell12309, BstLean.Part263.envelope, parameters]

theorem repair12309Cells (j : Fin 43) :
    0 ≤ cap12309 j ∧
    BstLean.Part263.envelope 12309 (parameters j) (scalarRow12309.table (sourceIndex j)).upper ≤ cap12309 j ∧
    (scalarRow12309.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12309 j + (scalarRow12309.table (sourceIndex j)).centre) /
      (scalarRow12309.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12309.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12309Cell0
  | ⟨1,_⟩ => exact repair12309Cell1
  | ⟨2,_⟩ => exact repair12309Cell2
  | ⟨3,_⟩ => exact repair12309Cell3
  | ⟨4,_⟩ => exact repair12309Cell4
  | ⟨5,_⟩ => exact repair12309Cell5
  | ⟨6,_⟩ => exact repair12309Cell6
  | ⟨7,_⟩ => exact repair12309Cell7
  | ⟨8,_⟩ => exact repair12309Cell8
  | ⟨9,_⟩ => exact repair12309Cell9
  | ⟨10,_⟩ => exact repair12309Cell10
  | ⟨11,_⟩ => exact repair12309Cell11
  | ⟨12,_⟩ => exact repair12309Cell12
  | ⟨13,_⟩ => exact repair12309Cell13
  | ⟨14,_⟩ => exact repair12309Cell14
  | ⟨15,_⟩ => exact repair12309Cell15
  | ⟨16,_⟩ => exact repair12309Cell16
  | ⟨17,_⟩ => exact repair12309Cell17
  | ⟨18,_⟩ => exact repair12309Cell18
  | ⟨19,_⟩ => exact repair12309Cell19
  | ⟨20,_⟩ => exact repair12309Cell20
  | ⟨21,_⟩ => exact repair12309Cell21
  | ⟨22,_⟩ => exact repair12309Cell22
  | ⟨23,_⟩ => exact repair12309Cell23
  | ⟨24,_⟩ => exact repair12309Cell24
  | ⟨25,_⟩ => exact repair12309Cell25
  | ⟨26,_⟩ => exact repair12309Cell26
  | ⟨27,_⟩ => exact repair12309Cell27
  | ⟨28,_⟩ => exact repair12309Cell28
  | ⟨29,_⟩ => exact repair12309Cell29
  | ⟨30,_⟩ => exact repair12309Cell30
  | ⟨31,_⟩ => exact repair12309Cell31
  | ⟨32,_⟩ => exact repair12309Cell32
  | ⟨33,_⟩ => exact repair12309Cell33
  | ⟨34,_⟩ => exact repair12309Cell34
  | ⟨35,_⟩ => exact repair12309Cell35
  | ⟨36,_⟩ => exact repair12309Cell36
  | ⟨37,_⟩ => exact repair12309Cell37
  | ⟨38,_⟩ => exact repair12309Cell38
  | ⟨39,_⟩ => exact repair12309Cell39
  | ⟨40,_⟩ => exact repair12309Cell40
  | ⟨41,_⟩ => exact repair12309Cell41
  | ⟨42,_⟩ => exact repair12309Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12309 : FrameRepair 12309 scalarRow12309 where
  cap := cap12309
  cap_nonneg := fun j => (repair12309Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12309])
  endpoint := fun j => (repair12309Cells j).2.1
  endpoint_upper := fun j => (repair12309Cells j).2.2.1
  frame := fun j => (repair12309Cells j).2.2.2

noncomputable def cap12310 : Fin 43 → ℝ
  | ⟨0,_⟩ => (4311661 / 15625000 : ℝ)
  | ⟨1,_⟩ => (8635907 / 31250000 : ℝ)
  | ⟨2,_⟩ => (276750751 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (6928787 / 25000000 : ℝ)
  | ⟨4,_⟩ => (138775609 / 500000000 : ℝ)
  | ⟨5,_⟩ => (17371873 / 62500000 : ℝ)
  | ⟨6,_⟩ => (34793407 / 125000000 : ℝ)
  | ⟨7,_⟩ => (278744039 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139569923 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279534681 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (139964273 / 500000000 : ℝ)
  | ⟨11,_⟩ => (140160481 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280712901 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140551697 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281493819 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (56376629 / 200000000 : ℝ)
  | ⟨16,_⟩ => (35283941 / 125000000 : ℝ)
  | ⟨17,_⟩ => (282658981 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141522747 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283431079 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141907869 / 500000000 : ℝ)
  | ⟨21,_⟩ => (7104987 / 25000000 : ℝ)
  | ⟨22,_⟩ => (142291149 / 500000000 : ℝ)
  | ⟨23,_⟩ => (142481853 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285344701 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (17857771 / 62500000 : ℝ)
  | ⟨26,_⟩ => (143051783 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286481397 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (71714583 / 250000000 : ℝ)
  | ⟨29,_⟩ => (71808593 / 250000000 : ℝ)
  | ⟨30,_⟩ => (143804509 / 500000000 : ℝ)
  | ⟨31,_⟩ => (3599791 / 12500000 : ℝ)
  | ⟨32,_⟩ => (144178331 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288728653 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (28909977 / 100000000 : ℝ)
  | ⟨35,_⟩ => (57894003 / 200000000 : ℝ)
  | ⟨36,_⟩ => (289839383 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290207893 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145287769 / 500000000 : ℝ)
  | ⟨39,_⟩ => (29094181 / 100000000 : ℝ)
  | ⟨40,_⟩ => (36413403 / 125000000 : ℝ)
  | ⟨41,_⟩ => (291671787 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (146017749 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12310Cell0 :
    0 ≤ cap12310 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨0,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12310 ⟨0,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨0,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell1 :
    0 ≤ cap12310 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨1,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12310 ⟨1,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨1,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell2 :
    0 ≤ cap12310 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨2,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12310 ⟨2,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨2,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell3 :
    0 ≤ cap12310 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨3,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12310 ⟨3,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨3,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell4 :
    0 ≤ cap12310 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨4,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12310 ⟨4,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨4,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell5 :
    0 ≤ cap12310 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨5,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12310 ⟨5,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨5,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell6 :
    0 ≤ cap12310 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨6,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12310 ⟨6,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨6,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell7 :
    0 ≤ cap12310 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨7,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12310 ⟨7,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨7,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell8 :
    0 ≤ cap12310 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨8,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12310 ⟨8,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨8,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell9 :
    0 ≤ cap12310 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨9,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12310 ⟨9,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨9,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell10 :
    0 ≤ cap12310 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨10,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12310 ⟨10,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨10,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell11 :
    0 ≤ cap12310 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨11,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12310 ⟨11,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨11,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell12 :
    0 ≤ cap12310 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨12,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12310 ⟨12,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨12,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell13 :
    0 ≤ cap12310 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨13,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12310 ⟨13,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨13,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell14 :
    0 ≤ cap12310 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨14,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12310 ⟨14,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨14,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell15 :
    0 ≤ cap12310 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨15,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12310 ⟨15,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨15,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell16 :
    0 ≤ cap12310 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨16,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12310 ⟨16,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨16,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell17 :
    0 ≤ cap12310 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨17,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12310 ⟨17,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨17,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell18 :
    0 ≤ cap12310 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨18,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12310 ⟨18,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨18,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell19 :
    0 ≤ cap12310 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨19,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12310 ⟨19,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨19,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell20 :
    0 ≤ cap12310 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨20,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12310 ⟨20,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨20,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell21 :
    0 ≤ cap12310 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨21,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12310 ⟨21,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨21,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell22 :
    0 ≤ cap12310 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨22,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12310 ⟨22,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨22,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell23 :
    0 ≤ cap12310 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨23,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12310 ⟨23,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨23,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell24 :
    0 ≤ cap12310 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨24,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12310 ⟨24,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨24,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell25 :
    0 ≤ cap12310 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨25,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12310 ⟨25,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨25,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell26 :
    0 ≤ cap12310 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨26,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12310 ⟨26,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨26,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell27 :
    0 ≤ cap12310 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨27,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12310 ⟨27,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨27,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell28 :
    0 ≤ cap12310 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨28,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12310 ⟨28,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨28,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell29 :
    0 ≤ cap12310 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨29,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12310 ⟨29,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨29,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell30 :
    0 ≤ cap12310 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨30,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12310 ⟨30,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨30,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell31 :
    0 ≤ cap12310 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨31,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12310 ⟨31,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨31,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell32 :
    0 ≤ cap12310 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨32,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12310 ⟨32,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨32,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell33 :
    0 ≤ cap12310 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨33,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12310 ⟨33,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨33,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell34 :
    0 ≤ cap12310 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨34,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12310 ⟨34,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨34,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell35 :
    0 ≤ cap12310 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨35,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12310 ⟨35,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨35,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell36 :
    0 ≤ cap12310 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨36,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12310 ⟨36,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨36,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell37 :
    0 ≤ cap12310 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨37,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12310 ⟨37,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨37,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell38 :
    0 ≤ cap12310 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨38,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12310 ⟨38,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨38,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell39 :
    0 ≤ cap12310 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨39,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12310 ⟨39,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨39,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell40 :
    0 ≤ cap12310 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨40,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12310 ⟨40,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨40,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell41 :
    0 ≤ cap12310 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨41,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12310 ⟨41,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨41,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cell42 :
    0 ≤ cap12310 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12310 (parameters ⟨42,by decide⟩)
      (scalarRow12310.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12310 ⟨42,by decide⟩ ∧
    (scalarRow12310.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 ⟨42,by decide⟩ + (scalarRow12310.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12310.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12310.targetFrame := by
  norm_num [cap12310, scalarRow12310, sourceIndex, cell12310, BstLean.Part263.envelope, parameters]

theorem repair12310Cells (j : Fin 43) :
    0 ≤ cap12310 j ∧
    BstLean.Part263.envelope 12310 (parameters j) (scalarRow12310.table (sourceIndex j)).upper ≤ cap12310 j ∧
    (scalarRow12310.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12310 j + (scalarRow12310.table (sourceIndex j)).centre) /
      (scalarRow12310.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12310.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12310Cell0
  | ⟨1,_⟩ => exact repair12310Cell1
  | ⟨2,_⟩ => exact repair12310Cell2
  | ⟨3,_⟩ => exact repair12310Cell3
  | ⟨4,_⟩ => exact repair12310Cell4
  | ⟨5,_⟩ => exact repair12310Cell5
  | ⟨6,_⟩ => exact repair12310Cell6
  | ⟨7,_⟩ => exact repair12310Cell7
  | ⟨8,_⟩ => exact repair12310Cell8
  | ⟨9,_⟩ => exact repair12310Cell9
  | ⟨10,_⟩ => exact repair12310Cell10
  | ⟨11,_⟩ => exact repair12310Cell11
  | ⟨12,_⟩ => exact repair12310Cell12
  | ⟨13,_⟩ => exact repair12310Cell13
  | ⟨14,_⟩ => exact repair12310Cell14
  | ⟨15,_⟩ => exact repair12310Cell15
  | ⟨16,_⟩ => exact repair12310Cell16
  | ⟨17,_⟩ => exact repair12310Cell17
  | ⟨18,_⟩ => exact repair12310Cell18
  | ⟨19,_⟩ => exact repair12310Cell19
  | ⟨20,_⟩ => exact repair12310Cell20
  | ⟨21,_⟩ => exact repair12310Cell21
  | ⟨22,_⟩ => exact repair12310Cell22
  | ⟨23,_⟩ => exact repair12310Cell23
  | ⟨24,_⟩ => exact repair12310Cell24
  | ⟨25,_⟩ => exact repair12310Cell25
  | ⟨26,_⟩ => exact repair12310Cell26
  | ⟨27,_⟩ => exact repair12310Cell27
  | ⟨28,_⟩ => exact repair12310Cell28
  | ⟨29,_⟩ => exact repair12310Cell29
  | ⟨30,_⟩ => exact repair12310Cell30
  | ⟨31,_⟩ => exact repair12310Cell31
  | ⟨32,_⟩ => exact repair12310Cell32
  | ⟨33,_⟩ => exact repair12310Cell33
  | ⟨34,_⟩ => exact repair12310Cell34
  | ⟨35,_⟩ => exact repair12310Cell35
  | ⟨36,_⟩ => exact repair12310Cell36
  | ⟨37,_⟩ => exact repair12310Cell37
  | ⟨38,_⟩ => exact repair12310Cell38
  | ⟨39,_⟩ => exact repair12310Cell39
  | ⟨40,_⟩ => exact repair12310Cell40
  | ⟨41,_⟩ => exact repair12310Cell41
  | ⟨42,_⟩ => exact repair12310Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12310 : FrameRepair 12310 scalarRow12310 where
  cap := cap12310
  cap_nonneg := fun j => (repair12310Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12310])
  endpoint := fun j => (repair12310Cells j).2.1
  endpoint_upper := fun j => (repair12310Cells j).2.2.1
  frame := fun j => (repair12310Cells j).2.2.2

noncomputable def cap12311 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275946229 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276348943 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276750663 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (55430277 / 200000000 : ℝ)
  | ⟨4,_⟩ => (277551117 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (13897493 / 50000000 : ℝ)
  | ⟨6,_⟩ => (139173571 / 500000000 : ℝ)
  | ⟨7,_⟩ => (278743919 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (6978493 / 25000000 : ℝ)
  | ⟨9,_⟩ => (69883637 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279928407 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280320817 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280712749 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (56220647 / 200000000 : ℝ)
  | ⟨14,_⟩ => (56298731 / 200000000 : ℝ)
  | ⟨15,_⟩ => (140941487 / 500000000 : ℝ)
  | ⟨16,_⟩ => (35283919 / 125000000 : ℝ)
  | ⟨17,_⟩ => (141329399 / 500000000 : ℝ)
  | ⟨18,_⟩ => (56609061 / 200000000 : ℝ)
  | ⟨19,_⟩ => (70857721 / 250000000 : ℝ)
  | ⟨20,_⟩ => (17738471 / 62500000 : ℝ)
  | ⟨21,_⟩ => (35524909 / 125000000 : ℝ)
  | ⟨22,_⟩ => (71145521 / 250000000 : ℝ)
  | ⟨23,_⟩ => (56992697 / 200000000 : ℝ)
  | ⟨24,_⟩ => (11413779 / 40000000 : ℝ)
  | ⟨25,_⟩ => (285724103 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286103327 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (1119067 / 3906250 : ℝ)
  | ⟨28,_⟩ => (286858081 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (57446823 / 200000000 : ℝ)
  | ⟨30,_⟩ => (57521751 / 200000000 : ℝ)
  | ⟨31,_⟩ => (287983011 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (144178193 / 500000000 : ℝ)
  | ⟨33,_⟩ => (72182093 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144549741 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289469721 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (72459771 / 250000000 : ℝ)
  | ⟨37,_⟩ => (72551897 / 250000000 : ℝ)
  | ⟨38,_⟩ => (145287613 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290941493 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291306901 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145835729 / 500000000 : ℝ)
  | ⟨42,_⟩ => (146017581 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12311Cell0 :
    0 ≤ cap12311 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨0,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12311 ⟨0,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨0,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell1 :
    0 ≤ cap12311 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨1,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12311 ⟨1,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨1,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell2 :
    0 ≤ cap12311 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨2,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12311 ⟨2,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨2,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell3 :
    0 ≤ cap12311 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨3,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12311 ⟨3,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨3,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell4 :
    0 ≤ cap12311 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨4,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12311 ⟨4,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨4,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell5 :
    0 ≤ cap12311 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨5,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12311 ⟨5,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨5,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell6 :
    0 ≤ cap12311 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨6,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12311 ⟨6,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨6,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell7 :
    0 ≤ cap12311 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨7,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12311 ⟨7,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨7,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell8 :
    0 ≤ cap12311 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨8,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12311 ⟨8,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨8,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell9 :
    0 ≤ cap12311 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨9,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12311 ⟨9,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨9,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell10 :
    0 ≤ cap12311 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨10,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12311 ⟨10,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨10,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell11 :
    0 ≤ cap12311 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨11,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12311 ⟨11,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨11,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell12 :
    0 ≤ cap12311 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨12,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12311 ⟨12,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨12,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell13 :
    0 ≤ cap12311 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨13,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12311 ⟨13,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨13,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell14 :
    0 ≤ cap12311 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨14,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12311 ⟨14,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨14,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell15 :
    0 ≤ cap12311 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨15,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12311 ⟨15,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨15,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell16 :
    0 ≤ cap12311 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨16,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12311 ⟨16,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨16,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell17 :
    0 ≤ cap12311 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨17,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12311 ⟨17,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨17,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell18 :
    0 ≤ cap12311 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨18,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12311 ⟨18,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨18,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell19 :
    0 ≤ cap12311 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨19,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12311 ⟨19,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨19,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell20 :
    0 ≤ cap12311 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨20,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12311 ⟨20,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨20,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell21 :
    0 ≤ cap12311 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨21,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12311 ⟨21,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨21,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell22 :
    0 ≤ cap12311 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨22,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12311 ⟨22,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨22,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell23 :
    0 ≤ cap12311 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨23,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12311 ⟨23,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨23,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell24 :
    0 ≤ cap12311 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨24,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12311 ⟨24,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨24,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell25 :
    0 ≤ cap12311 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨25,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12311 ⟨25,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨25,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell26 :
    0 ≤ cap12311 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨26,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12311 ⟨26,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨26,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell27 :
    0 ≤ cap12311 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨27,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12311 ⟨27,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨27,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell28 :
    0 ≤ cap12311 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨28,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12311 ⟨28,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨28,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell29 :
    0 ≤ cap12311 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨29,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12311 ⟨29,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨29,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell30 :
    0 ≤ cap12311 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨30,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12311 ⟨30,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨30,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell31 :
    0 ≤ cap12311 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨31,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12311 ⟨31,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨31,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell32 :
    0 ≤ cap12311 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨32,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12311 ⟨32,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨32,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell33 :
    0 ≤ cap12311 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨33,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12311 ⟨33,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨33,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell34 :
    0 ≤ cap12311 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨34,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12311 ⟨34,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨34,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell35 :
    0 ≤ cap12311 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨35,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12311 ⟨35,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨35,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell36 :
    0 ≤ cap12311 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨36,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12311 ⟨36,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨36,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell37 :
    0 ≤ cap12311 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨37,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12311 ⟨37,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨37,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell38 :
    0 ≤ cap12311 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨38,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12311 ⟨38,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨38,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell39 :
    0 ≤ cap12311 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨39,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12311 ⟨39,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨39,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell40 :
    0 ≤ cap12311 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨40,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12311 ⟨40,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨40,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell41 :
    0 ≤ cap12311 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨41,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12311 ⟨41,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨41,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cell42 :
    0 ≤ cap12311 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12311 (parameters ⟨42,by decide⟩)
      (scalarRow12311.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12311 ⟨42,by decide⟩ ∧
    (scalarRow12311.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 ⟨42,by decide⟩ + (scalarRow12311.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12311.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12311.targetFrame := by
  norm_num [cap12311, scalarRow12311, sourceIndex, cell12311, BstLean.Part263.envelope, parameters]

theorem repair12311Cells (j : Fin 43) :
    0 ≤ cap12311 j ∧
    BstLean.Part263.envelope 12311 (parameters j) (scalarRow12311.table (sourceIndex j)).upper ≤ cap12311 j ∧
    (scalarRow12311.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12311 j + (scalarRow12311.table (sourceIndex j)).centre) /
      (scalarRow12311.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12311.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12311Cell0
  | ⟨1,_⟩ => exact repair12311Cell1
  | ⟨2,_⟩ => exact repair12311Cell2
  | ⟨3,_⟩ => exact repair12311Cell3
  | ⟨4,_⟩ => exact repair12311Cell4
  | ⟨5,_⟩ => exact repair12311Cell5
  | ⟨6,_⟩ => exact repair12311Cell6
  | ⟨7,_⟩ => exact repair12311Cell7
  | ⟨8,_⟩ => exact repair12311Cell8
  | ⟨9,_⟩ => exact repair12311Cell9
  | ⟨10,_⟩ => exact repair12311Cell10
  | ⟨11,_⟩ => exact repair12311Cell11
  | ⟨12,_⟩ => exact repair12311Cell12
  | ⟨13,_⟩ => exact repair12311Cell13
  | ⟨14,_⟩ => exact repair12311Cell14
  | ⟨15,_⟩ => exact repair12311Cell15
  | ⟨16,_⟩ => exact repair12311Cell16
  | ⟨17,_⟩ => exact repair12311Cell17
  | ⟨18,_⟩ => exact repair12311Cell18
  | ⟨19,_⟩ => exact repair12311Cell19
  | ⟨20,_⟩ => exact repair12311Cell20
  | ⟨21,_⟩ => exact repair12311Cell21
  | ⟨22,_⟩ => exact repair12311Cell22
  | ⟨23,_⟩ => exact repair12311Cell23
  | ⟨24,_⟩ => exact repair12311Cell24
  | ⟨25,_⟩ => exact repair12311Cell25
  | ⟨26,_⟩ => exact repair12311Cell26
  | ⟨27,_⟩ => exact repair12311Cell27
  | ⟨28,_⟩ => exact repair12311Cell28
  | ⟨29,_⟩ => exact repair12311Cell29
  | ⟨30,_⟩ => exact repair12311Cell30
  | ⟨31,_⟩ => exact repair12311Cell31
  | ⟨32,_⟩ => exact repair12311Cell32
  | ⟨33,_⟩ => exact repair12311Cell33
  | ⟨34,_⟩ => exact repair12311Cell34
  | ⟨35,_⟩ => exact repair12311Cell35
  | ⟨36,_⟩ => exact repair12311Cell36
  | ⟨37,_⟩ => exact repair12311Cell37
  | ⟨38,_⟩ => exact repair12311Cell38
  | ⟨39,_⟩ => exact repair12311Cell39
  | ⟨40,_⟩ => exact repair12311Cell40
  | ⟨41,_⟩ => exact repair12311Cell41
  | ⟨42,_⟩ => exact repair12311Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12311 : FrameRepair 12311 scalarRow12311 where
  cap := cap12311
  cap_nonneg := fun j => (repair12311Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12311])
  endpoint := fun j => (repair12311Cells j).2.1
  endpoint_upper := fun j => (repair12311Cells j).2.2.1
  frame := fun j => (repair12311Cells j).2.2.2

noncomputable def cap12312 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137973077 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276348861 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138375287 / 500000000 : ℝ)
  | ⟨3,_⟩ => (27715129 / 100000000 : ℝ)
  | ⟨4,_⟩ => (34693877 / 125000000 : ℝ)
  | ⟨5,_⟩ => (277949753 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278347029 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278743799 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279139593 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (17470901 / 62500000 : ℝ)
  | ⟨10,_⟩ => (279928267 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280320671 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140356299 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281103077 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (28149349 / 100000000 : ℝ)
  | ⟨15,_⟩ => (70470701 / 250000000 : ℝ)
  | ⟨16,_⟩ => (11290847 / 40000000 : ℝ)
  | ⟨17,_⟩ => (141329307 / 500000000 : ℝ)
  | ⟨18,_⟩ => (56609023 / 200000000 : ℝ)
  | ⟨19,_⟩ => (8857209 / 31250000 : ℝ)
  | ⟨20,_⟩ => (141907667 / 500000000 : ℝ)
  | ⟨21,_⟩ => (35524883 / 125000000 : ℝ)
  | ⟨22,_⟩ => (28458187 / 100000000 : ℝ)
  | ⟨23,_⟩ => (56992653 / 200000000 : ℝ)
  | ⟨24,_⟩ => (35668031 / 125000000 : ℝ)
  | ⟨25,_⟩ => (285723871 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286103089 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (71620227 / 250000000 : ℝ)
  | ⟨28,_⟩ => (28685783 / 100000000 : ℝ)
  | ⟨29,_⟩ => (143616929 / 500000000 : ℝ)
  | ⟨30,_⟩ => (71902123 / 250000000 : ℝ)
  | ⟨31,_⟩ => (143991371 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288356111 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (28872809 / 100000000 : ℝ)
  | ⟨34,_⟩ => (57819839 / 200000000 : ℝ)
  | ⟨35,_⟩ => (72367357 / 250000000 : ℝ)
  | ⟨36,_⟩ => (57967757 / 200000000 : ℝ)
  | ⟨37,_⟩ => (145103641 / 500000000 : ℝ)
  | ⟨38,_⟩ => (58114983 / 200000000 : ℝ)
  | ⟨39,_⟩ => (36367647 / 125000000 : ℝ)
  | ⟨40,_⟩ => (145653289 / 500000000 : ℝ)
  | ⟨41,_⟩ => (36458891 / 125000000 : ℝ)
  | ⟨42,_⟩ => (292034827 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12312Cell0 :
    0 ≤ cap12312 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨0,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12312 ⟨0,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨0,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell1 :
    0 ≤ cap12312 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨1,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12312 ⟨1,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨1,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell2 :
    0 ≤ cap12312 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨2,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12312 ⟨2,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨2,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell3 :
    0 ≤ cap12312 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨3,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12312 ⟨3,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨3,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell4 :
    0 ≤ cap12312 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨4,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12312 ⟨4,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨4,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell5 :
    0 ≤ cap12312 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨5,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12312 ⟨5,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨5,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell6 :
    0 ≤ cap12312 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨6,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12312 ⟨6,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨6,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell7 :
    0 ≤ cap12312 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨7,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12312 ⟨7,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨7,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell8 :
    0 ≤ cap12312 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨8,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12312 ⟨8,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨8,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell9 :
    0 ≤ cap12312 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨9,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12312 ⟨9,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨9,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell10 :
    0 ≤ cap12312 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨10,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12312 ⟨10,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨10,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell11 :
    0 ≤ cap12312 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨11,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12312 ⟨11,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨11,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell12 :
    0 ≤ cap12312 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨12,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12312 ⟨12,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨12,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell13 :
    0 ≤ cap12312 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨13,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12312 ⟨13,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨13,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell14 :
    0 ≤ cap12312 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨14,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12312 ⟨14,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨14,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell15 :
    0 ≤ cap12312 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨15,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12312 ⟨15,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨15,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell16 :
    0 ≤ cap12312 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨16,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12312 ⟨16,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨16,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell17 :
    0 ≤ cap12312 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨17,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12312 ⟨17,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨17,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell18 :
    0 ≤ cap12312 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨18,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12312 ⟨18,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨18,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell19 :
    0 ≤ cap12312 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨19,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12312 ⟨19,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨19,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell20 :
    0 ≤ cap12312 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨20,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12312 ⟨20,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨20,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell21 :
    0 ≤ cap12312 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨21,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12312 ⟨21,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨21,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell22 :
    0 ≤ cap12312 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨22,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12312 ⟨22,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨22,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell23 :
    0 ≤ cap12312 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨23,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12312 ⟨23,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨23,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell24 :
    0 ≤ cap12312 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨24,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12312 ⟨24,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨24,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell25 :
    0 ≤ cap12312 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨25,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12312 ⟨25,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨25,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell26 :
    0 ≤ cap12312 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨26,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12312 ⟨26,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨26,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell27 :
    0 ≤ cap12312 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨27,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12312 ⟨27,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨27,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell28 :
    0 ≤ cap12312 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨28,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12312 ⟨28,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨28,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell29 :
    0 ≤ cap12312 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨29,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12312 ⟨29,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨29,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell30 :
    0 ≤ cap12312 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨30,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12312 ⟨30,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨30,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell31 :
    0 ≤ cap12312 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨31,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12312 ⟨31,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨31,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell32 :
    0 ≤ cap12312 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨32,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12312 ⟨32,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨32,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell33 :
    0 ≤ cap12312 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨33,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12312 ⟨33,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨33,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell34 :
    0 ≤ cap12312 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨34,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12312 ⟨34,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨34,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell35 :
    0 ≤ cap12312 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨35,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12312 ⟨35,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨35,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell36 :
    0 ≤ cap12312 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨36,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12312 ⟨36,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨36,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell37 :
    0 ≤ cap12312 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨37,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12312 ⟨37,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨37,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell38 :
    0 ≤ cap12312 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨38,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12312 ⟨38,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨38,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell39 :
    0 ≤ cap12312 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨39,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12312 ⟨39,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨39,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell40 :
    0 ≤ cap12312 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨40,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12312 ⟨40,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨40,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell41 :
    0 ≤ cap12312 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨41,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12312 ⟨41,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨41,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cell42 :
    0 ≤ cap12312 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12312 (parameters ⟨42,by decide⟩)
      (scalarRow12312.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12312 ⟨42,by decide⟩ ∧
    (scalarRow12312.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 ⟨42,by decide⟩ + (scalarRow12312.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12312.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12312.targetFrame := by
  norm_num [cap12312, scalarRow12312, sourceIndex, cell12312, BstLean.Part263.envelope, parameters]

theorem repair12312Cells (j : Fin 43) :
    0 ≤ cap12312 j ∧
    BstLean.Part263.envelope 12312 (parameters j) (scalarRow12312.table (sourceIndex j)).upper ≤ cap12312 j ∧
    (scalarRow12312.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12312 j + (scalarRow12312.table (sourceIndex j)).centre) /
      (scalarRow12312.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12312.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12312Cell0
  | ⟨1,_⟩ => exact repair12312Cell1
  | ⟨2,_⟩ => exact repair12312Cell2
  | ⟨3,_⟩ => exact repair12312Cell3
  | ⟨4,_⟩ => exact repair12312Cell4
  | ⟨5,_⟩ => exact repair12312Cell5
  | ⟨6,_⟩ => exact repair12312Cell6
  | ⟨7,_⟩ => exact repair12312Cell7
  | ⟨8,_⟩ => exact repair12312Cell8
  | ⟨9,_⟩ => exact repair12312Cell9
  | ⟨10,_⟩ => exact repair12312Cell10
  | ⟨11,_⟩ => exact repair12312Cell11
  | ⟨12,_⟩ => exact repair12312Cell12
  | ⟨13,_⟩ => exact repair12312Cell13
  | ⟨14,_⟩ => exact repair12312Cell14
  | ⟨15,_⟩ => exact repair12312Cell15
  | ⟨16,_⟩ => exact repair12312Cell16
  | ⟨17,_⟩ => exact repair12312Cell17
  | ⟨18,_⟩ => exact repair12312Cell18
  | ⟨19,_⟩ => exact repair12312Cell19
  | ⟨20,_⟩ => exact repair12312Cell20
  | ⟨21,_⟩ => exact repair12312Cell21
  | ⟨22,_⟩ => exact repair12312Cell22
  | ⟨23,_⟩ => exact repair12312Cell23
  | ⟨24,_⟩ => exact repair12312Cell24
  | ⟨25,_⟩ => exact repair12312Cell25
  | ⟨26,_⟩ => exact repair12312Cell26
  | ⟨27,_⟩ => exact repair12312Cell27
  | ⟨28,_⟩ => exact repair12312Cell28
  | ⟨29,_⟩ => exact repair12312Cell29
  | ⟨30,_⟩ => exact repair12312Cell30
  | ⟨31,_⟩ => exact repair12312Cell31
  | ⟨32,_⟩ => exact repair12312Cell32
  | ⟨33,_⟩ => exact repair12312Cell33
  | ⟨34,_⟩ => exact repair12312Cell34
  | ⟨35,_⟩ => exact repair12312Cell35
  | ⟨36,_⟩ => exact repair12312Cell36
  | ⟨37,_⟩ => exact repair12312Cell37
  | ⟨38,_⟩ => exact repair12312Cell38
  | ⟨39,_⟩ => exact repair12312Cell39
  | ⟨40,_⟩ => exact repair12312Cell40
  | ⟨41,_⟩ => exact repair12312Cell41
  | ⟨42,_⟩ => exact repair12312Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12312 : FrameRepair 12312 scalarRow12312 where
  cap := cap12312
  cap_nonneg := fun j => (repair12312Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12312])
  endpoint := fun j => (repair12312Cells j).2.1
  endpoint_upper := fun j => (repair12312Cells j).2.2.1
  frame := fun j => (repair12312Cells j).2.2.2

noncomputable def cap12313 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275946079 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276348779 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138375243 / 500000000 : ℝ)
  | ⟨3,_⟩ => (69287799 / 250000000 : ℝ)
  | ⟨4,_⟩ => (55510183 / 200000000 : ℝ)
  | ⟨5,_⟩ => (55589929 / 200000000 : ℝ)
  | ⟨6,_⟩ => (55669383 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278743679 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279139467 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279534283 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (4373877 / 15625000 : ℝ)
  | ⟨11,_⟩ => (140160263 / 500000000 : ℝ)
  | ⟨12,_⟩ => (140356223 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281102919 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140746663 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281882633 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (141135499 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282658431 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141522463 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283430493 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (70953783 / 250000000 : ℝ)
  | ⟨21,_⟩ => (35524857 / 125000000 : ℝ)
  | ⟨22,_⟩ => (56916331 / 200000000 : ℝ)
  | ⟨23,_⟩ => (56992609 / 200000000 : ℝ)
  | ⟨24,_⟩ => (142672011 / 500000000 : ℝ)
  | ⟨25,_⟩ => (142861819 / 500000000 : ℝ)
  | ⟨26,_⟩ => (5722057 / 20000000 : ℝ)
  | ⟨27,_⟩ => (286480663 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286857579 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287233601 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287608229 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287982473 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72088959 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288727809 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72274727 / 250000000 : ℝ)
  | ⟨35,_⟩ => (57893827 / 200000000 : ℝ)
  | ⟨36,_⟩ => (144919243 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290206977 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (72643651 / 250000000 : ℝ)
  | ⟨39,_⟩ => (290940859 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58261251 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291670799 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (73008623 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12313Cell0 :
    0 ≤ cap12313 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨0,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12313 ⟨0,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨0,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell1 :
    0 ≤ cap12313 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨1,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12313 ⟨1,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨1,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell2 :
    0 ≤ cap12313 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨2,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12313 ⟨2,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨2,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell3 :
    0 ≤ cap12313 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨3,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12313 ⟨3,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨3,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell4 :
    0 ≤ cap12313 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨4,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12313 ⟨4,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨4,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell5 :
    0 ≤ cap12313 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨5,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12313 ⟨5,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨5,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell6 :
    0 ≤ cap12313 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨6,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12313 ⟨6,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨6,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell7 :
    0 ≤ cap12313 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨7,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12313 ⟨7,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨7,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell8 :
    0 ≤ cap12313 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨8,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12313 ⟨8,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨8,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell9 :
    0 ≤ cap12313 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨9,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12313 ⟨9,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨9,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell10 :
    0 ≤ cap12313 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨10,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12313 ⟨10,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨10,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell11 :
    0 ≤ cap12313 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨11,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12313 ⟨11,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨11,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell12 :
    0 ≤ cap12313 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨12,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12313 ⟨12,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨12,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell13 :
    0 ≤ cap12313 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨13,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12313 ⟨13,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨13,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell14 :
    0 ≤ cap12313 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨14,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12313 ⟨14,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨14,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell15 :
    0 ≤ cap12313 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨15,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12313 ⟨15,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨15,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell16 :
    0 ≤ cap12313 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨16,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12313 ⟨16,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨16,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell17 :
    0 ≤ cap12313 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨17,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12313 ⟨17,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨17,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell18 :
    0 ≤ cap12313 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨18,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12313 ⟨18,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨18,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell19 :
    0 ≤ cap12313 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨19,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12313 ⟨19,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨19,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell20 :
    0 ≤ cap12313 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨20,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12313 ⟨20,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨20,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell21 :
    0 ≤ cap12313 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨21,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12313 ⟨21,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨21,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell22 :
    0 ≤ cap12313 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨22,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12313 ⟨22,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨22,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell23 :
    0 ≤ cap12313 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨23,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12313 ⟨23,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨23,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell24 :
    0 ≤ cap12313 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨24,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12313 ⟨24,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨24,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell25 :
    0 ≤ cap12313 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨25,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12313 ⟨25,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨25,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell26 :
    0 ≤ cap12313 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨26,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12313 ⟨26,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨26,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell27 :
    0 ≤ cap12313 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨27,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12313 ⟨27,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨27,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell28 :
    0 ≤ cap12313 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨28,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12313 ⟨28,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨28,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell29 :
    0 ≤ cap12313 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨29,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12313 ⟨29,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨29,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell30 :
    0 ≤ cap12313 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨30,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12313 ⟨30,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨30,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell31 :
    0 ≤ cap12313 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨31,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12313 ⟨31,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨31,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell32 :
    0 ≤ cap12313 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨32,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12313 ⟨32,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨32,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell33 :
    0 ≤ cap12313 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨33,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12313 ⟨33,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨33,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell34 :
    0 ≤ cap12313 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨34,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12313 ⟨34,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨34,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell35 :
    0 ≤ cap12313 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨35,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12313 ⟨35,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨35,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell36 :
    0 ≤ cap12313 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨36,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12313 ⟨36,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨36,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell37 :
    0 ≤ cap12313 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨37,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12313 ⟨37,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨37,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell38 :
    0 ≤ cap12313 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨38,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12313 ⟨38,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨38,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell39 :
    0 ≤ cap12313 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨39,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12313 ⟨39,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨39,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell40 :
    0 ≤ cap12313 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨40,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12313 ⟨40,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨40,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell41 :
    0 ≤ cap12313 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨41,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12313 ⟨41,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨41,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cell42 :
    0 ≤ cap12313 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12313 (parameters ⟨42,by decide⟩)
      (scalarRow12313.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12313 ⟨42,by decide⟩ ∧
    (scalarRow12313.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 ⟨42,by decide⟩ + (scalarRow12313.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12313.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12313.targetFrame := by
  norm_num [cap12313, scalarRow12313, sourceIndex, cell12313, BstLean.Part263.envelope, parameters]

theorem repair12313Cells (j : Fin 43) :
    0 ≤ cap12313 j ∧
    BstLean.Part263.envelope 12313 (parameters j) (scalarRow12313.table (sourceIndex j)).upper ≤ cap12313 j ∧
    (scalarRow12313.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12313 j + (scalarRow12313.table (sourceIndex j)).centre) /
      (scalarRow12313.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12313.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12313Cell0
  | ⟨1,_⟩ => exact repair12313Cell1
  | ⟨2,_⟩ => exact repair12313Cell2
  | ⟨3,_⟩ => exact repair12313Cell3
  | ⟨4,_⟩ => exact repair12313Cell4
  | ⟨5,_⟩ => exact repair12313Cell5
  | ⟨6,_⟩ => exact repair12313Cell6
  | ⟨7,_⟩ => exact repair12313Cell7
  | ⟨8,_⟩ => exact repair12313Cell8
  | ⟨9,_⟩ => exact repair12313Cell9
  | ⟨10,_⟩ => exact repair12313Cell10
  | ⟨11,_⟩ => exact repair12313Cell11
  | ⟨12,_⟩ => exact repair12313Cell12
  | ⟨13,_⟩ => exact repair12313Cell13
  | ⟨14,_⟩ => exact repair12313Cell14
  | ⟨15,_⟩ => exact repair12313Cell15
  | ⟨16,_⟩ => exact repair12313Cell16
  | ⟨17,_⟩ => exact repair12313Cell17
  | ⟨18,_⟩ => exact repair12313Cell18
  | ⟨19,_⟩ => exact repair12313Cell19
  | ⟨20,_⟩ => exact repair12313Cell20
  | ⟨21,_⟩ => exact repair12313Cell21
  | ⟨22,_⟩ => exact repair12313Cell22
  | ⟨23,_⟩ => exact repair12313Cell23
  | ⟨24,_⟩ => exact repair12313Cell24
  | ⟨25,_⟩ => exact repair12313Cell25
  | ⟨26,_⟩ => exact repair12313Cell26
  | ⟨27,_⟩ => exact repair12313Cell27
  | ⟨28,_⟩ => exact repair12313Cell28
  | ⟨29,_⟩ => exact repair12313Cell29
  | ⟨30,_⟩ => exact repair12313Cell30
  | ⟨31,_⟩ => exact repair12313Cell31
  | ⟨32,_⟩ => exact repair12313Cell32
  | ⟨33,_⟩ => exact repair12313Cell33
  | ⟨34,_⟩ => exact repair12313Cell34
  | ⟨35,_⟩ => exact repair12313Cell35
  | ⟨36,_⟩ => exact repair12313Cell36
  | ⟨37,_⟩ => exact repair12313Cell37
  | ⟨38,_⟩ => exact repair12313Cell38
  | ⟨39,_⟩ => exact repair12313Cell39
  | ⟨40,_⟩ => exact repair12313Cell40
  | ⟨41,_⟩ => exact repair12313Cell41
  | ⟨42,_⟩ => exact repair12313Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12313 : FrameRepair 12313 scalarRow12313 where
  cap := cap12313
  cap_nonneg := fun j => (repair12313Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12313])
  endpoint := fun j => (repair12313Cells j).2.1
  endpoint_upper := fun j => (repair12313Cells j).2.2.1
  frame := fun j => (repair12313Cells j).2.2.2

noncomputable def cap12314 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275946003 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138174349 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138375199 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277151101 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138775407 / 500000000 : ℝ)
  | ⟨5,_⟩ => (138974769 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278346801 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139371779 / 500000000 : ℝ)
  | ⟨8,_⟩ => (13956967 / 50000000 : ℝ)
  | ⟨9,_⟩ => (5590683 / 20000000 : ℝ)
  | ⟨10,_⟩ => (279927989 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (14016019 / 50000000 : ℝ)
  | ⟨12,_⟩ => (140356147 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281102761 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140746581 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140941231 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282270821 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (35332281 / 125000000 : ℝ)
  | ⟨18,_⟩ => (283044737 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283430297 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (28381493 / 100000000 : ℝ)
  | ⟨21,_⟩ => (35524831 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284581441 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (35620353 / 125000000 : ℝ)
  | ⟨24,_⟩ => (57068759 / 200000000 : ℝ)
  | ⟨25,_⟩ => (57144681 / 200000000 : ℝ)
  | ⟨26,_⟩ => (286102611 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143240209 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286857329 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (4488021 / 15625000 : ℝ)
  | ⟨30,_⟩ => (143803983 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287982203 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288355561 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (36090941 / 125000000 : ℝ)
  | ⟨34,_⟩ => (289098621 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144734421 / 500000000 : ℝ)
  | ⟨36,_⟩ => (144919093 / 500000000 : ℝ)
  | ⟨37,_⟩ => (18137917 / 62500000 : ℝ)
  | ⟨38,_⟩ => (290574293 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290940541 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (72826483 / 250000000 : ℝ)
  | ⟨41,_⟩ => (29167047 / 100000000 : ℝ)
  | ⟨42,_⟩ => (146017079 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12314Cell0 :
    0 ≤ cap12314 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨0,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12314 ⟨0,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨0,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell1 :
    0 ≤ cap12314 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨1,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12314 ⟨1,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨1,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell2 :
    0 ≤ cap12314 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨2,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12314 ⟨2,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨2,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell3 :
    0 ≤ cap12314 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨3,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12314 ⟨3,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨3,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell4 :
    0 ≤ cap12314 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨4,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12314 ⟨4,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨4,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell5 :
    0 ≤ cap12314 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨5,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12314 ⟨5,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨5,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell6 :
    0 ≤ cap12314 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨6,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12314 ⟨6,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨6,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell7 :
    0 ≤ cap12314 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨7,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12314 ⟨7,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨7,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell8 :
    0 ≤ cap12314 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨8,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12314 ⟨8,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨8,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell9 :
    0 ≤ cap12314 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨9,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12314 ⟨9,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨9,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell10 :
    0 ≤ cap12314 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨10,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12314 ⟨10,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨10,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell11 :
    0 ≤ cap12314 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨11,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12314 ⟨11,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨11,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell12 :
    0 ≤ cap12314 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨12,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12314 ⟨12,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨12,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell13 :
    0 ≤ cap12314 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨13,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12314 ⟨13,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨13,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell14 :
    0 ≤ cap12314 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨14,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12314 ⟨14,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨14,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell15 :
    0 ≤ cap12314 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨15,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12314 ⟨15,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨15,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell16 :
    0 ≤ cap12314 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨16,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12314 ⟨16,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨16,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell17 :
    0 ≤ cap12314 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨17,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12314 ⟨17,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨17,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell18 :
    0 ≤ cap12314 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨18,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12314 ⟨18,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨18,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell19 :
    0 ≤ cap12314 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨19,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12314 ⟨19,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨19,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell20 :
    0 ≤ cap12314 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨20,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12314 ⟨20,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨20,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell21 :
    0 ≤ cap12314 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨21,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12314 ⟨21,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨21,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell22 :
    0 ≤ cap12314 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨22,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12314 ⟨22,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨22,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell23 :
    0 ≤ cap12314 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨23,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12314 ⟨23,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨23,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell24 :
    0 ≤ cap12314 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨24,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12314 ⟨24,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨24,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell25 :
    0 ≤ cap12314 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨25,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12314 ⟨25,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨25,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell26 :
    0 ≤ cap12314 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨26,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12314 ⟨26,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨26,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell27 :
    0 ≤ cap12314 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨27,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12314 ⟨27,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨27,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell28 :
    0 ≤ cap12314 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨28,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12314 ⟨28,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨28,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell29 :
    0 ≤ cap12314 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨29,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12314 ⟨29,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨29,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell30 :
    0 ≤ cap12314 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨30,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12314 ⟨30,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨30,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell31 :
    0 ≤ cap12314 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨31,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12314 ⟨31,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨31,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell32 :
    0 ≤ cap12314 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨32,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12314 ⟨32,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨32,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell33 :
    0 ≤ cap12314 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨33,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12314 ⟨33,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨33,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell34 :
    0 ≤ cap12314 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨34,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12314 ⟨34,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨34,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell35 :
    0 ≤ cap12314 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨35,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12314 ⟨35,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨35,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell36 :
    0 ≤ cap12314 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨36,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12314 ⟨36,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨36,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell37 :
    0 ≤ cap12314 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨37,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12314 ⟨37,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨37,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell38 :
    0 ≤ cap12314 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨38,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12314 ⟨38,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨38,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell39 :
    0 ≤ cap12314 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨39,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12314 ⟨39,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨39,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell40 :
    0 ≤ cap12314 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨40,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12314 ⟨40,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨40,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell41 :
    0 ≤ cap12314 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨41,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12314 ⟨41,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨41,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cell42 :
    0 ≤ cap12314 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12314 (parameters ⟨42,by decide⟩)
      (scalarRow12314.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12314 ⟨42,by decide⟩ ∧
    (scalarRow12314.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 ⟨42,by decide⟩ + (scalarRow12314.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12314.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12314.targetFrame := by
  norm_num [cap12314, scalarRow12314, sourceIndex, cell12314, BstLean.Part263.envelope, parameters]

theorem repair12314Cells (j : Fin 43) :
    0 ≤ cap12314 j ∧
    BstLean.Part263.envelope 12314 (parameters j) (scalarRow12314.table (sourceIndex j)).upper ≤ cap12314 j ∧
    (scalarRow12314.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12314 j + (scalarRow12314.table (sourceIndex j)).centre) /
      (scalarRow12314.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12314.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12314Cell0
  | ⟨1,_⟩ => exact repair12314Cell1
  | ⟨2,_⟩ => exact repair12314Cell2
  | ⟨3,_⟩ => exact repair12314Cell3
  | ⟨4,_⟩ => exact repair12314Cell4
  | ⟨5,_⟩ => exact repair12314Cell5
  | ⟨6,_⟩ => exact repair12314Cell6
  | ⟨7,_⟩ => exact repair12314Cell7
  | ⟨8,_⟩ => exact repair12314Cell8
  | ⟨9,_⟩ => exact repair12314Cell9
  | ⟨10,_⟩ => exact repair12314Cell10
  | ⟨11,_⟩ => exact repair12314Cell11
  | ⟨12,_⟩ => exact repair12314Cell12
  | ⟨13,_⟩ => exact repair12314Cell13
  | ⟨14,_⟩ => exact repair12314Cell14
  | ⟨15,_⟩ => exact repair12314Cell15
  | ⟨16,_⟩ => exact repair12314Cell16
  | ⟨17,_⟩ => exact repair12314Cell17
  | ⟨18,_⟩ => exact repair12314Cell18
  | ⟨19,_⟩ => exact repair12314Cell19
  | ⟨20,_⟩ => exact repair12314Cell20
  | ⟨21,_⟩ => exact repair12314Cell21
  | ⟨22,_⟩ => exact repair12314Cell22
  | ⟨23,_⟩ => exact repair12314Cell23
  | ⟨24,_⟩ => exact repair12314Cell24
  | ⟨25,_⟩ => exact repair12314Cell25
  | ⟨26,_⟩ => exact repair12314Cell26
  | ⟨27,_⟩ => exact repair12314Cell27
  | ⟨28,_⟩ => exact repair12314Cell28
  | ⟨29,_⟩ => exact repair12314Cell29
  | ⟨30,_⟩ => exact repair12314Cell30
  | ⟨31,_⟩ => exact repair12314Cell31
  | ⟨32,_⟩ => exact repair12314Cell32
  | ⟨33,_⟩ => exact repair12314Cell33
  | ⟨34,_⟩ => exact repair12314Cell34
  | ⟨35,_⟩ => exact repair12314Cell35
  | ⟨36,_⟩ => exact repair12314Cell36
  | ⟨37,_⟩ => exact repair12314Cell37
  | ⟨38,_⟩ => exact repair12314Cell38
  | ⟨39,_⟩ => exact repair12314Cell39
  | ⟨40,_⟩ => exact repair12314Cell40
  | ⟨41,_⟩ => exact repair12314Cell41
  | ⟨42,_⟩ => exact repair12314Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12314 : FrameRepair 12314 scalarRow12314 where
  cap := cap12314
  cap_nonneg := fun j => (repair12314Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12314])
  endpoint := fun j => (repair12314Cells j).2.1
  endpoint_upper := fun j => (repair12314Cells j).2.2.1
  frame := fun j => (repair12314Cells j).2.2.2

noncomputable def cap12315 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34493241 / 125000000 : ℝ)
  | ⟨1,_⟩ => (34543577 / 125000000 : ℝ)
  | ⟨2,_⟩ => (27675031 / 100000000 : ℝ)
  | ⟨3,_⟩ => (277151007 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138775357 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277949431 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278346687 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139371719 / 500000000 : ℝ)
  | ⟨8,_⟩ => (139569607 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279534017 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (5598557 / 20000000 : ℝ)
  | ⟨11,_⟩ => (56064047 / 200000000 : ℝ)
  | ⟨12,_⟩ => (140356071 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281102603 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281492997 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70470573 / 250000000 : ℝ)
  | ⟨16,_⟩ => (70567661 / 250000000 : ℝ)
  | ⟨17,_⟩ => (56531613 / 200000000 : ℝ)
  | ⟨18,_⟩ => (283044547 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283430101 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283814729 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (7104961 / 25000000 : ℝ)
  | ⟨22,_⟩ => (284581227 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (71240651 / 250000000 : ℝ)
  | ⟨24,_⟩ => (285343569 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285723173 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286102373 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286480173 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143428539 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287233087 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287607703 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143990967 / 500000000 : ℝ)
  | ⟨32,_⟩ => (144177643 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288727247 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289098333 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72367137 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289837887 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290206367 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145286991 / 500000000 : ℝ)
  | ⟨39,_⟩ => (4545941 / 15625000 : ℝ)
  | ⟨40,_⟩ => (36413201 / 125000000 : ℝ)
  | ⟨41,_⟩ => (291670141 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292033823 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12315Cell0 :
    0 ≤ cap12315 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨0,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12315 ⟨0,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨0,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell1 :
    0 ≤ cap12315 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨1,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12315 ⟨1,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨1,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell2 :
    0 ≤ cap12315 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨2,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12315 ⟨2,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨2,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell3 :
    0 ≤ cap12315 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨3,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12315 ⟨3,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨3,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell4 :
    0 ≤ cap12315 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨4,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12315 ⟨4,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨4,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell5 :
    0 ≤ cap12315 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨5,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12315 ⟨5,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨5,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell6 :
    0 ≤ cap12315 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨6,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12315 ⟨6,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨6,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell7 :
    0 ≤ cap12315 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨7,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12315 ⟨7,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨7,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell8 :
    0 ≤ cap12315 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨8,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12315 ⟨8,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨8,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell9 :
    0 ≤ cap12315 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨9,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12315 ⟨9,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨9,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell10 :
    0 ≤ cap12315 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨10,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12315 ⟨10,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨10,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell11 :
    0 ≤ cap12315 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨11,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12315 ⟨11,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨11,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell12 :
    0 ≤ cap12315 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨12,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12315 ⟨12,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨12,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell13 :
    0 ≤ cap12315 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨13,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12315 ⟨13,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨13,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell14 :
    0 ≤ cap12315 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨14,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12315 ⟨14,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨14,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell15 :
    0 ≤ cap12315 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨15,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12315 ⟨15,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨15,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell16 :
    0 ≤ cap12315 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨16,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12315 ⟨16,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨16,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell17 :
    0 ≤ cap12315 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨17,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12315 ⟨17,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨17,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell18 :
    0 ≤ cap12315 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨18,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12315 ⟨18,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨18,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell19 :
    0 ≤ cap12315 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨19,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12315 ⟨19,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨19,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell20 :
    0 ≤ cap12315 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨20,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12315 ⟨20,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨20,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell21 :
    0 ≤ cap12315 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨21,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12315 ⟨21,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨21,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell22 :
    0 ≤ cap12315 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨22,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12315 ⟨22,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨22,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell23 :
    0 ≤ cap12315 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨23,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12315 ⟨23,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨23,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell24 :
    0 ≤ cap12315 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨24,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12315 ⟨24,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨24,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell25 :
    0 ≤ cap12315 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨25,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12315 ⟨25,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨25,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell26 :
    0 ≤ cap12315 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨26,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12315 ⟨26,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨26,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell27 :
    0 ≤ cap12315 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨27,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12315 ⟨27,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨27,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell28 :
    0 ≤ cap12315 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨28,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12315 ⟨28,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨28,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell29 :
    0 ≤ cap12315 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨29,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12315 ⟨29,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨29,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell30 :
    0 ≤ cap12315 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨30,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12315 ⟨30,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨30,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell31 :
    0 ≤ cap12315 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨31,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12315 ⟨31,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨31,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell32 :
    0 ≤ cap12315 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨32,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12315 ⟨32,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨32,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell33 :
    0 ≤ cap12315 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨33,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12315 ⟨33,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨33,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell34 :
    0 ≤ cap12315 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨34,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12315 ⟨34,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨34,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell35 :
    0 ≤ cap12315 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨35,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12315 ⟨35,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨35,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell36 :
    0 ≤ cap12315 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨36,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12315 ⟨36,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨36,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell37 :
    0 ≤ cap12315 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨37,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12315 ⟨37,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨37,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell38 :
    0 ≤ cap12315 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨38,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12315 ⟨38,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨38,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell39 :
    0 ≤ cap12315 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨39,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12315 ⟨39,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨39,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell40 :
    0 ≤ cap12315 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨40,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12315 ⟨40,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨40,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell41 :
    0 ≤ cap12315 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨41,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12315 ⟨41,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨41,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cell42 :
    0 ≤ cap12315 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12315 (parameters ⟨42,by decide⟩)
      (scalarRow12315.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12315 ⟨42,by decide⟩ ∧
    (scalarRow12315.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 ⟨42,by decide⟩ + (scalarRow12315.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12315.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12315.targetFrame := by
  norm_num [cap12315, scalarRow12315, sourceIndex, cell12315, BstLean.Part263.envelope, parameters]

theorem repair12315Cells (j : Fin 43) :
    0 ≤ cap12315 j ∧
    BstLean.Part263.envelope 12315 (parameters j) (scalarRow12315.table (sourceIndex j)).upper ≤ cap12315 j ∧
    (scalarRow12315.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12315 j + (scalarRow12315.table (sourceIndex j)).centre) /
      (scalarRow12315.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12315.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12315Cell0
  | ⟨1,_⟩ => exact repair12315Cell1
  | ⟨2,_⟩ => exact repair12315Cell2
  | ⟨3,_⟩ => exact repair12315Cell3
  | ⟨4,_⟩ => exact repair12315Cell4
  | ⟨5,_⟩ => exact repair12315Cell5
  | ⟨6,_⟩ => exact repair12315Cell6
  | ⟨7,_⟩ => exact repair12315Cell7
  | ⟨8,_⟩ => exact repair12315Cell8
  | ⟨9,_⟩ => exact repair12315Cell9
  | ⟨10,_⟩ => exact repair12315Cell10
  | ⟨11,_⟩ => exact repair12315Cell11
  | ⟨12,_⟩ => exact repair12315Cell12
  | ⟨13,_⟩ => exact repair12315Cell13
  | ⟨14,_⟩ => exact repair12315Cell14
  | ⟨15,_⟩ => exact repair12315Cell15
  | ⟨16,_⟩ => exact repair12315Cell16
  | ⟨17,_⟩ => exact repair12315Cell17
  | ⟨18,_⟩ => exact repair12315Cell18
  | ⟨19,_⟩ => exact repair12315Cell19
  | ⟨20,_⟩ => exact repair12315Cell20
  | ⟨21,_⟩ => exact repair12315Cell21
  | ⟨22,_⟩ => exact repair12315Cell22
  | ⟨23,_⟩ => exact repair12315Cell23
  | ⟨24,_⟩ => exact repair12315Cell24
  | ⟨25,_⟩ => exact repair12315Cell25
  | ⟨26,_⟩ => exact repair12315Cell26
  | ⟨27,_⟩ => exact repair12315Cell27
  | ⟨28,_⟩ => exact repair12315Cell28
  | ⟨29,_⟩ => exact repair12315Cell29
  | ⟨30,_⟩ => exact repair12315Cell30
  | ⟨31,_⟩ => exact repair12315Cell31
  | ⟨32,_⟩ => exact repair12315Cell32
  | ⟨33,_⟩ => exact repair12315Cell33
  | ⟨34,_⟩ => exact repair12315Cell34
  | ⟨35,_⟩ => exact repair12315Cell35
  | ⟨36,_⟩ => exact repair12315Cell36
  | ⟨37,_⟩ => exact repair12315Cell37
  | ⟨38,_⟩ => exact repair12315Cell38
  | ⟨39,_⟩ => exact repair12315Cell39
  | ⟨40,_⟩ => exact repair12315Cell40
  | ⟨41,_⟩ => exact repair12315Cell41
  | ⟨42,_⟩ => exact repair12315Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12315 : FrameRepair 12315 scalarRow12315 where
  cap := cap12315
  cap_nonneg := fun j => (repair12315Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12315])
  endpoint := fun j => (repair12315Cells j).2.1
  endpoint_upper := fun j => (repair12315Cells j).2.2.1
  frame := fun j => (repair12315Cells j).2.2.2

noncomputable def cap12316 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275945853 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (55269707 / 200000000 : ℝ)
  | ⟨2,_⟩ => (138375111 / 500000000 : ℝ)
  | ⟨3,_⟩ => (4330483 / 15625000 : ℝ)
  | ⟨4,_⟩ => (277550613 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277949323 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139173287 / 500000000 : ℝ)
  | ⟨7,_⟩ => (139371659 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279139087 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69883471 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279927711 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280320089 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (28071199 / 100000000 : ℝ)
  | ⟨13,_⟩ => (56220489 / 200000000 : ℝ)
  | ⟨14,_⟩ => (281492833 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281882121 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282270467 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141328941 / 500000000 : ℝ)
  | ⟨18,_⟩ => (141522179 / 500000000 : ℝ)
  | ⟨19,_⟩ => (141714953 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283814527 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (35524779 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284581013 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (17810149 / 62500000 : ℝ)
  | ⟨24,_⟩ => (142671671 / 500000000 : ℝ)
  | ⟨25,_⟩ => (14286147 / 50000000 : ℝ)
  | ⟨26,_⟩ => (143051067 / 500000000 : ℝ)
  | ⟨27,_⟩ => (35809991 / 125000000 : ℝ)
  | ⟨28,_⟩ => (286856827 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (28723283 / 100000000 : ℝ)
  | ⟨30,_⟩ => (3595093 / 12500000 : ℝ)
  | ⟨31,_⟩ => (57596333 / 200000000 : ℝ)
  | ⟨32,_⟩ => (28835501 / 100000000 : ℝ)
  | ⟨33,_⟩ => (144363483 / 500000000 : ℝ)
  | ⟨34,_⟩ => (144549023 / 500000000 : ℝ)
  | ⟨35,_⟩ => (57893651 / 200000000 : ℝ)
  | ⟨36,_⟩ => (72459397 / 250000000 : ℝ)
  | ⟨37,_⟩ => (145103031 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290573671 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290939907 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58261057 / 200000000 : ℝ)
  | ⟨41,_⟩ => (72917453 / 250000000 : ℝ)
  | ⟨42,_⟩ => (18252093 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12316Cell0 :
    0 ≤ cap12316 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨0,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12316 ⟨0,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨0,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell1 :
    0 ≤ cap12316 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨1,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12316 ⟨1,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨1,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell2 :
    0 ≤ cap12316 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨2,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12316 ⟨2,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨2,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell3 :
    0 ≤ cap12316 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨3,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12316 ⟨3,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨3,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell4 :
    0 ≤ cap12316 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨4,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12316 ⟨4,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨4,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell5 :
    0 ≤ cap12316 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨5,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12316 ⟨5,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨5,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell6 :
    0 ≤ cap12316 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨6,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12316 ⟨6,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨6,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell7 :
    0 ≤ cap12316 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨7,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12316 ⟨7,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨7,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell8 :
    0 ≤ cap12316 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨8,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12316 ⟨8,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨8,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell9 :
    0 ≤ cap12316 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨9,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12316 ⟨9,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨9,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell10 :
    0 ≤ cap12316 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨10,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12316 ⟨10,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨10,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell11 :
    0 ≤ cap12316 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨11,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12316 ⟨11,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨11,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell12 :
    0 ≤ cap12316 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨12,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12316 ⟨12,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨12,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell13 :
    0 ≤ cap12316 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨13,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12316 ⟨13,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨13,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell14 :
    0 ≤ cap12316 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨14,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12316 ⟨14,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨14,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell15 :
    0 ≤ cap12316 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨15,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12316 ⟨15,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨15,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell16 :
    0 ≤ cap12316 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨16,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12316 ⟨16,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨16,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell17 :
    0 ≤ cap12316 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨17,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12316 ⟨17,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨17,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell18 :
    0 ≤ cap12316 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨18,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12316 ⟨18,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨18,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell19 :
    0 ≤ cap12316 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨19,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12316 ⟨19,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨19,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell20 :
    0 ≤ cap12316 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨20,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12316 ⟨20,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨20,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell21 :
    0 ≤ cap12316 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨21,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12316 ⟨21,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨21,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell22 :
    0 ≤ cap12316 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨22,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12316 ⟨22,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨22,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell23 :
    0 ≤ cap12316 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨23,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12316 ⟨23,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨23,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell24 :
    0 ≤ cap12316 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨24,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12316 ⟨24,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨24,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell25 :
    0 ≤ cap12316 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨25,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12316 ⟨25,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨25,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell26 :
    0 ≤ cap12316 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨26,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12316 ⟨26,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨26,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell27 :
    0 ≤ cap12316 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨27,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12316 ⟨27,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨27,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell28 :
    0 ≤ cap12316 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨28,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12316 ⟨28,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨28,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell29 :
    0 ≤ cap12316 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨29,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12316 ⟨29,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨29,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell30 :
    0 ≤ cap12316 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨30,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12316 ⟨30,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨30,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell31 :
    0 ≤ cap12316 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨31,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12316 ⟨31,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨31,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell32 :
    0 ≤ cap12316 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨32,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12316 ⟨32,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨32,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell33 :
    0 ≤ cap12316 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨33,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12316 ⟨33,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨33,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell34 :
    0 ≤ cap12316 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨34,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12316 ⟨34,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨34,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell35 :
    0 ≤ cap12316 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨35,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12316 ⟨35,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨35,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell36 :
    0 ≤ cap12316 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨36,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12316 ⟨36,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨36,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell37 :
    0 ≤ cap12316 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨37,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12316 ⟨37,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨37,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell38 :
    0 ≤ cap12316 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨38,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12316 ⟨38,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨38,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell39 :
    0 ≤ cap12316 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨39,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12316 ⟨39,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨39,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell40 :
    0 ≤ cap12316 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨40,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12316 ⟨40,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨40,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell41 :
    0 ≤ cap12316 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨41,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12316 ⟨41,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨41,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cell42 :
    0 ≤ cap12316 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12316 (parameters ⟨42,by decide⟩)
      (scalarRow12316.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12316 ⟨42,by decide⟩ ∧
    (scalarRow12316.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 ⟨42,by decide⟩ + (scalarRow12316.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12316.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12316.targetFrame := by
  norm_num [cap12316, scalarRow12316, sourceIndex, cell12316, BstLean.Part263.envelope, parameters]

theorem repair12316Cells (j : Fin 43) :
    0 ≤ cap12316 j ∧
    BstLean.Part263.envelope 12316 (parameters j) (scalarRow12316.table (sourceIndex j)).upper ≤ cap12316 j ∧
    (scalarRow12316.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12316 j + (scalarRow12316.table (sourceIndex j)).centre) /
      (scalarRow12316.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12316.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12316Cell0
  | ⟨1,_⟩ => exact repair12316Cell1
  | ⟨2,_⟩ => exact repair12316Cell2
  | ⟨3,_⟩ => exact repair12316Cell3
  | ⟨4,_⟩ => exact repair12316Cell4
  | ⟨5,_⟩ => exact repair12316Cell5
  | ⟨6,_⟩ => exact repair12316Cell6
  | ⟨7,_⟩ => exact repair12316Cell7
  | ⟨8,_⟩ => exact repair12316Cell8
  | ⟨9,_⟩ => exact repair12316Cell9
  | ⟨10,_⟩ => exact repair12316Cell10
  | ⟨11,_⟩ => exact repair12316Cell11
  | ⟨12,_⟩ => exact repair12316Cell12
  | ⟨13,_⟩ => exact repair12316Cell13
  | ⟨14,_⟩ => exact repair12316Cell14
  | ⟨15,_⟩ => exact repair12316Cell15
  | ⟨16,_⟩ => exact repair12316Cell16
  | ⟨17,_⟩ => exact repair12316Cell17
  | ⟨18,_⟩ => exact repair12316Cell18
  | ⟨19,_⟩ => exact repair12316Cell19
  | ⟨20,_⟩ => exact repair12316Cell20
  | ⟨21,_⟩ => exact repair12316Cell21
  | ⟨22,_⟩ => exact repair12316Cell22
  | ⟨23,_⟩ => exact repair12316Cell23
  | ⟨24,_⟩ => exact repair12316Cell24
  | ⟨25,_⟩ => exact repair12316Cell25
  | ⟨26,_⟩ => exact repair12316Cell26
  | ⟨27,_⟩ => exact repair12316Cell27
  | ⟨28,_⟩ => exact repair12316Cell28
  | ⟨29,_⟩ => exact repair12316Cell29
  | ⟨30,_⟩ => exact repair12316Cell30
  | ⟨31,_⟩ => exact repair12316Cell31
  | ⟨32,_⟩ => exact repair12316Cell32
  | ⟨33,_⟩ => exact repair12316Cell33
  | ⟨34,_⟩ => exact repair12316Cell34
  | ⟨35,_⟩ => exact repair12316Cell35
  | ⟨36,_⟩ => exact repair12316Cell36
  | ⟨37,_⟩ => exact repair12316Cell37
  | ⟨38,_⟩ => exact repair12316Cell38
  | ⟨39,_⟩ => exact repair12316Cell39
  | ⟨40,_⟩ => exact repair12316Cell40
  | ⟨41,_⟩ => exact repair12316Cell41
  | ⟨42,_⟩ => exact repair12316Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12316 : FrameRepair 12316 scalarRow12316 where
  cap := cap12316
  cap_nonneg := fun j => (repair12316Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12316])
  endpoint := fun j => (repair12316Cells j).2.1
  endpoint_upper := fun j => (repair12316Cells j).2.2.1
  frame := fun j => (repair12316Cells j).2.2.2

noncomputable def cap12317 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137972889 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276348453 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138375067 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138575409 / 500000000 : ℝ)
  | ⟨4,_⟩ => (17346907 / 62500000 : ℝ)
  | ⟨5,_⟩ => (8685913 / 31250000 : ℝ)
  | ⟨6,_⟩ => (13917323 / 50000000 : ℝ)
  | ⟨7,_⟩ => (139371599 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279138961 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (34941719 / 125000000 : ℝ)
  | ⟨10,_⟩ => (69981893 / 250000000 : ℝ)
  | ⟨11,_⟩ => (35039993 / 125000000 : ℝ)
  | ⟨12,_⟩ => (280711839 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281102287 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281492669 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281881951 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (28227029 / 100000000 : ℝ)
  | ⟨17,_⟩ => (282657699 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283044169 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (28342971 / 100000000 : ℝ)
  | ⟨20,_⟩ => (11352573 / 40000000 : ℝ)
  | ⟨21,_⟩ => (35524753 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284580799 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (71240541 / 250000000 : ℝ)
  | ⟨24,_⟩ => (71335779 / 250000000 : ℝ)
  | ⟨25,_⟩ => (71430677 / 250000000 : ℝ)
  | ⟨26,_⟩ => (57220379 / 200000000 : ℝ)
  | ⟨27,_⟩ => (71619921 / 250000000 : ℝ)
  | ⟨28,_⟩ => (2241067 / 7812500 : ℝ)
  | ⟨29,_⟩ => (287232573 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287607177 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (71995349 / 250000000 : ℝ)
  | ⟨32,_⟩ => (57670947 / 200000000 : ℝ)
  | ⟨33,_⟩ => (57745337 / 200000000 : ℝ)
  | ⟨34,_⟩ => (289097759 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144733981 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289837289 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290205757 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (3632167 / 12500000 : ℝ)
  | ⟨39,_⟩ => (29093959 / 100000000 : ℝ)
  | ⟨40,_⟩ => (291304963 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (72917371 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292033153 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12317Cell0 :
    0 ≤ cap12317 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨0,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12317 ⟨0,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨0,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell1 :
    0 ≤ cap12317 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨1,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12317 ⟨1,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨1,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell2 :
    0 ≤ cap12317 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨2,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12317 ⟨2,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨2,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell3 :
    0 ≤ cap12317 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨3,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12317 ⟨3,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨3,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell4 :
    0 ≤ cap12317 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨4,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12317 ⟨4,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨4,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell5 :
    0 ≤ cap12317 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨5,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12317 ⟨5,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨5,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell6 :
    0 ≤ cap12317 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨6,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12317 ⟨6,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨6,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell7 :
    0 ≤ cap12317 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨7,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12317 ⟨7,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨7,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell8 :
    0 ≤ cap12317 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨8,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12317 ⟨8,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨8,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell9 :
    0 ≤ cap12317 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨9,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12317 ⟨9,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨9,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell10 :
    0 ≤ cap12317 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨10,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12317 ⟨10,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨10,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell11 :
    0 ≤ cap12317 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨11,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12317 ⟨11,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨11,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell12 :
    0 ≤ cap12317 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨12,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12317 ⟨12,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨12,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell13 :
    0 ≤ cap12317 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨13,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12317 ⟨13,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨13,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell14 :
    0 ≤ cap12317 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨14,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12317 ⟨14,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨14,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell15 :
    0 ≤ cap12317 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨15,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12317 ⟨15,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨15,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell16 :
    0 ≤ cap12317 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨16,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12317 ⟨16,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨16,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell17 :
    0 ≤ cap12317 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨17,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12317 ⟨17,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨17,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell18 :
    0 ≤ cap12317 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨18,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12317 ⟨18,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨18,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell19 :
    0 ≤ cap12317 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨19,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12317 ⟨19,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨19,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell20 :
    0 ≤ cap12317 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨20,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12317 ⟨20,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨20,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell21 :
    0 ≤ cap12317 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨21,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12317 ⟨21,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨21,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell22 :
    0 ≤ cap12317 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨22,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12317 ⟨22,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨22,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell23 :
    0 ≤ cap12317 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨23,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12317 ⟨23,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨23,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell24 :
    0 ≤ cap12317 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨24,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12317 ⟨24,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨24,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell25 :
    0 ≤ cap12317 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨25,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12317 ⟨25,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨25,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell26 :
    0 ≤ cap12317 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨26,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12317 ⟨26,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨26,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell27 :
    0 ≤ cap12317 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨27,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12317 ⟨27,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨27,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell28 :
    0 ≤ cap12317 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨28,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12317 ⟨28,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨28,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell29 :
    0 ≤ cap12317 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨29,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12317 ⟨29,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨29,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell30 :
    0 ≤ cap12317 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨30,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12317 ⟨30,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨30,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell31 :
    0 ≤ cap12317 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨31,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12317 ⟨31,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨31,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell32 :
    0 ≤ cap12317 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨32,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12317 ⟨32,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨32,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell33 :
    0 ≤ cap12317 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨33,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12317 ⟨33,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨33,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell34 :
    0 ≤ cap12317 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨34,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12317 ⟨34,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨34,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell35 :
    0 ≤ cap12317 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨35,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12317 ⟨35,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨35,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell36 :
    0 ≤ cap12317 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨36,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12317 ⟨36,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨36,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell37 :
    0 ≤ cap12317 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨37,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12317 ⟨37,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨37,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell38 :
    0 ≤ cap12317 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨38,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12317 ⟨38,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨38,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell39 :
    0 ≤ cap12317 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨39,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12317 ⟨39,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨39,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell40 :
    0 ≤ cap12317 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨40,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12317 ⟨40,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨40,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell41 :
    0 ≤ cap12317 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨41,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12317 ⟨41,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨41,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cell42 :
    0 ≤ cap12317 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12317 (parameters ⟨42,by decide⟩)
      (scalarRow12317.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12317 ⟨42,by decide⟩ ∧
    (scalarRow12317.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 ⟨42,by decide⟩ + (scalarRow12317.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12317.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12317.targetFrame := by
  norm_num [cap12317, scalarRow12317, sourceIndex, cell12317, BstLean.Part263.envelope, parameters]

theorem repair12317Cells (j : Fin 43) :
    0 ≤ cap12317 j ∧
    BstLean.Part263.envelope 12317 (parameters j) (scalarRow12317.table (sourceIndex j)).upper ≤ cap12317 j ∧
    (scalarRow12317.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12317 j + (scalarRow12317.table (sourceIndex j)).centre) /
      (scalarRow12317.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12317.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12317Cell0
  | ⟨1,_⟩ => exact repair12317Cell1
  | ⟨2,_⟩ => exact repair12317Cell2
  | ⟨3,_⟩ => exact repair12317Cell3
  | ⟨4,_⟩ => exact repair12317Cell4
  | ⟨5,_⟩ => exact repair12317Cell5
  | ⟨6,_⟩ => exact repair12317Cell6
  | ⟨7,_⟩ => exact repair12317Cell7
  | ⟨8,_⟩ => exact repair12317Cell8
  | ⟨9,_⟩ => exact repair12317Cell9
  | ⟨10,_⟩ => exact repair12317Cell10
  | ⟨11,_⟩ => exact repair12317Cell11
  | ⟨12,_⟩ => exact repair12317Cell12
  | ⟨13,_⟩ => exact repair12317Cell13
  | ⟨14,_⟩ => exact repair12317Cell14
  | ⟨15,_⟩ => exact repair12317Cell15
  | ⟨16,_⟩ => exact repair12317Cell16
  | ⟨17,_⟩ => exact repair12317Cell17
  | ⟨18,_⟩ => exact repair12317Cell18
  | ⟨19,_⟩ => exact repair12317Cell19
  | ⟨20,_⟩ => exact repair12317Cell20
  | ⟨21,_⟩ => exact repair12317Cell21
  | ⟨22,_⟩ => exact repair12317Cell22
  | ⟨23,_⟩ => exact repair12317Cell23
  | ⟨24,_⟩ => exact repair12317Cell24
  | ⟨25,_⟩ => exact repair12317Cell25
  | ⟨26,_⟩ => exact repair12317Cell26
  | ⟨27,_⟩ => exact repair12317Cell27
  | ⟨28,_⟩ => exact repair12317Cell28
  | ⟨29,_⟩ => exact repair12317Cell29
  | ⟨30,_⟩ => exact repair12317Cell30
  | ⟨31,_⟩ => exact repair12317Cell31
  | ⟨32,_⟩ => exact repair12317Cell32
  | ⟨33,_⟩ => exact repair12317Cell33
  | ⟨34,_⟩ => exact repair12317Cell34
  | ⟨35,_⟩ => exact repair12317Cell35
  | ⟨36,_⟩ => exact repair12317Cell36
  | ⟨37,_⟩ => exact repair12317Cell37
  | ⟨38,_⟩ => exact repair12317Cell38
  | ⟨39,_⟩ => exact repair12317Cell39
  | ⟨40,_⟩ => exact repair12317Cell40
  | ⟨41,_⟩ => exact repair12317Cell41
  | ⟨42,_⟩ => exact repair12317Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12317 : FrameRepair 12317 scalarRow12317 where
  cap := cap12317
  cap_nonneg := fun j => (repair12317Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12317])
  endpoint := fun j => (repair12317Cells j).2.1
  endpoint_upper := fun j => (repair12317Cells j).2.2.1
  frame := fun j => (repair12317Cells j).2.2.2

noncomputable def cap12318 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275945703 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276348371 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138375023 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277150723 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277550411 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277949109 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139173173 / 500000000 : ℝ)
  | ⟨7,_⟩ => (139371539 / 500000000 : ℝ)
  | ⟨8,_⟩ => (139569417 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279533619 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279927433 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280319799 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280711687 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281102129 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (35186563 / 125000000 : ℝ)
  | ⟨15,_⟩ => (14094089 / 50000000 : ℝ)
  | ⟨16,_⟩ => (141135057 / 500000000 : ℝ)
  | ⟨17,_⟩ => (70664379 / 250000000 : ℝ)
  | ⟨18,_⟩ => (14152199 / 50000000 : ℝ)
  | ⟨19,_⟩ => (56685903 / 200000000 : ℝ)
  | ⟨20,_⟩ => (70953531 / 250000000 : ℝ)
  | ⟨21,_⟩ => (35524727 / 125000000 : ℝ)
  | ⟨22,_⟩ => (56916117 / 200000000 : ℝ)
  | ⟨23,_⟩ => (35620243 / 125000000 : ℝ)
  | ⟨24,_⟩ => (28534289 / 100000000 : ℝ)
  | ⟨25,_⟩ => (11428899 / 40000000 : ℝ)
  | ⟨26,_⟩ => (286101657 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286479439 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (11474253 / 40000000 : ℝ)
  | ⟨29,_⟩ => (71808079 / 250000000 : ℝ)
  | ⟨30,_⟩ => (143803457 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287981127 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (14417723 / 50000000 : ℝ)
  | ⟨33,_⟩ => (72181601 / 250000000 : ℝ)
  | ⟨34,_⟩ => (1129287 / 3906250 : ℝ)
  | ⟨35,_⟩ => (289467669 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (28983699 / 100000000 : ℝ)
  | ⟨37,_⟩ => (72551363 / 250000000 : ℝ)
  | ⟨38,_⟩ => (290573049 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290939273 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (910327 / 3125000 : ℝ)
  | ⟨41,_⟩ => (58333831 / 200000000 : ℝ)
  | ⟨42,_⟩ => (146016409 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12318Cell0 :
    0 ≤ cap12318 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨0,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12318 ⟨0,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨0,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell1 :
    0 ≤ cap12318 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨1,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12318 ⟨1,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨1,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell2 :
    0 ≤ cap12318 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨2,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12318 ⟨2,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨2,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell3 :
    0 ≤ cap12318 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨3,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12318 ⟨3,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨3,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell4 :
    0 ≤ cap12318 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨4,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12318 ⟨4,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨4,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell5 :
    0 ≤ cap12318 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨5,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12318 ⟨5,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨5,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell6 :
    0 ≤ cap12318 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨6,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12318 ⟨6,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨6,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell7 :
    0 ≤ cap12318 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨7,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12318 ⟨7,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨7,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell8 :
    0 ≤ cap12318 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨8,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12318 ⟨8,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨8,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell9 :
    0 ≤ cap12318 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨9,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12318 ⟨9,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨9,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell10 :
    0 ≤ cap12318 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨10,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12318 ⟨10,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨10,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell11 :
    0 ≤ cap12318 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨11,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12318 ⟨11,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨11,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell12 :
    0 ≤ cap12318 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨12,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12318 ⟨12,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨12,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell13 :
    0 ≤ cap12318 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨13,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12318 ⟨13,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨13,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell14 :
    0 ≤ cap12318 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨14,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12318 ⟨14,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨14,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell15 :
    0 ≤ cap12318 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨15,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12318 ⟨15,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨15,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell16 :
    0 ≤ cap12318 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨16,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12318 ⟨16,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨16,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell17 :
    0 ≤ cap12318 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨17,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12318 ⟨17,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨17,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell18 :
    0 ≤ cap12318 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨18,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12318 ⟨18,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨18,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell19 :
    0 ≤ cap12318 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨19,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12318 ⟨19,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨19,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell20 :
    0 ≤ cap12318 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨20,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12318 ⟨20,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨20,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell21 :
    0 ≤ cap12318 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨21,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12318 ⟨21,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨21,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell22 :
    0 ≤ cap12318 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨22,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12318 ⟨22,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨22,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell23 :
    0 ≤ cap12318 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨23,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12318 ⟨23,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨23,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell24 :
    0 ≤ cap12318 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨24,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12318 ⟨24,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨24,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell25 :
    0 ≤ cap12318 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨25,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12318 ⟨25,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨25,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell26 :
    0 ≤ cap12318 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨26,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12318 ⟨26,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨26,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell27 :
    0 ≤ cap12318 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨27,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12318 ⟨27,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨27,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell28 :
    0 ≤ cap12318 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨28,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12318 ⟨28,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨28,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell29 :
    0 ≤ cap12318 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨29,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12318 ⟨29,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨29,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell30 :
    0 ≤ cap12318 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨30,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12318 ⟨30,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨30,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell31 :
    0 ≤ cap12318 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨31,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12318 ⟨31,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨31,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell32 :
    0 ≤ cap12318 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨32,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12318 ⟨32,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨32,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell33 :
    0 ≤ cap12318 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨33,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12318 ⟨33,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨33,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell34 :
    0 ≤ cap12318 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨34,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12318 ⟨34,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨34,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell35 :
    0 ≤ cap12318 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨35,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12318 ⟨35,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨35,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell36 :
    0 ≤ cap12318 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨36,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12318 ⟨36,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨36,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell37 :
    0 ≤ cap12318 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨37,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12318 ⟨37,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨37,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell38 :
    0 ≤ cap12318 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨38,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12318 ⟨38,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨38,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell39 :
    0 ≤ cap12318 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨39,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12318 ⟨39,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨39,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell40 :
    0 ≤ cap12318 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨40,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12318 ⟨40,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨40,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell41 :
    0 ≤ cap12318 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨41,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12318 ⟨41,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨41,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cell42 :
    0 ≤ cap12318 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12318 (parameters ⟨42,by decide⟩)
      (scalarRow12318.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12318 ⟨42,by decide⟩ ∧
    (scalarRow12318.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 ⟨42,by decide⟩ + (scalarRow12318.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12318.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12318.targetFrame := by
  norm_num [cap12318, scalarRow12318, sourceIndex, cell12318, BstLean.Part263.envelope, parameters]

theorem repair12318Cells (j : Fin 43) :
    0 ≤ cap12318 j ∧
    BstLean.Part263.envelope 12318 (parameters j) (scalarRow12318.table (sourceIndex j)).upper ≤ cap12318 j ∧
    (scalarRow12318.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12318 j + (scalarRow12318.table (sourceIndex j)).centre) /
      (scalarRow12318.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12318.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12318Cell0
  | ⟨1,_⟩ => exact repair12318Cell1
  | ⟨2,_⟩ => exact repair12318Cell2
  | ⟨3,_⟩ => exact repair12318Cell3
  | ⟨4,_⟩ => exact repair12318Cell4
  | ⟨5,_⟩ => exact repair12318Cell5
  | ⟨6,_⟩ => exact repair12318Cell6
  | ⟨7,_⟩ => exact repair12318Cell7
  | ⟨8,_⟩ => exact repair12318Cell8
  | ⟨9,_⟩ => exact repair12318Cell9
  | ⟨10,_⟩ => exact repair12318Cell10
  | ⟨11,_⟩ => exact repair12318Cell11
  | ⟨12,_⟩ => exact repair12318Cell12
  | ⟨13,_⟩ => exact repair12318Cell13
  | ⟨14,_⟩ => exact repair12318Cell14
  | ⟨15,_⟩ => exact repair12318Cell15
  | ⟨16,_⟩ => exact repair12318Cell16
  | ⟨17,_⟩ => exact repair12318Cell17
  | ⟨18,_⟩ => exact repair12318Cell18
  | ⟨19,_⟩ => exact repair12318Cell19
  | ⟨20,_⟩ => exact repair12318Cell20
  | ⟨21,_⟩ => exact repair12318Cell21
  | ⟨22,_⟩ => exact repair12318Cell22
  | ⟨23,_⟩ => exact repair12318Cell23
  | ⟨24,_⟩ => exact repair12318Cell24
  | ⟨25,_⟩ => exact repair12318Cell25
  | ⟨26,_⟩ => exact repair12318Cell26
  | ⟨27,_⟩ => exact repair12318Cell27
  | ⟨28,_⟩ => exact repair12318Cell28
  | ⟨29,_⟩ => exact repair12318Cell29
  | ⟨30,_⟩ => exact repair12318Cell30
  | ⟨31,_⟩ => exact repair12318Cell31
  | ⟨32,_⟩ => exact repair12318Cell32
  | ⟨33,_⟩ => exact repair12318Cell33
  | ⟨34,_⟩ => exact repair12318Cell34
  | ⟨35,_⟩ => exact repair12318Cell35
  | ⟨36,_⟩ => exact repair12318Cell36
  | ⟨37,_⟩ => exact repair12318Cell37
  | ⟨38,_⟩ => exact repair12318Cell38
  | ⟨39,_⟩ => exact repair12318Cell39
  | ⟨40,_⟩ => exact repair12318Cell40
  | ⟨41,_⟩ => exact repair12318Cell41
  | ⟨42,_⟩ => exact repair12318Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12318 : FrameRepair 12318 scalarRow12318 where
  cap := cap12318
  cap_nonneg := fun j => (repair12318Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12318])
  endpoint := fun j => (repair12318Cells j).2.1
  endpoint_upper := fun j => (repair12318Cells j).2.2.1
  frame := fun j => (repair12318Cells j).2.2.2

noncomputable def cap12319 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68986407 / 250000000 : ℝ)
  | ⟨1,_⟩ => (27634829 / 100000000 : ℝ)
  | ⟨2,_⟩ => (138374979 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277150629 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (27755031 / 100000000 : ℝ)
  | ⟨5,_⟩ => (138974501 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278346233 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139371479 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69784677 / 250000000 : ℝ)
  | ⟨9,_⟩ => (139766743 / 500000000 : ℝ)
  | ⟨10,_⟩ => (139963647 / 500000000 : ℝ)
  | ⟨11,_⟩ => (280319653 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (56142307 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281101971 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (14074617 / 50000000 : ℝ)
  | ⟨15,_⟩ => (28188161 / 100000000 : ℝ)
  | ⟨16,_⟩ => (282269937 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282657333 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (28304379 / 100000000 : ℝ)
  | ⟨19,_⟩ => (7085733 / 25000000 : ℝ)
  | ⟨20,_⟩ => (141906961 / 500000000 : ℝ)
  | ⟨21,_⟩ => (35524701 / 125000000 : ℝ)
  | ⟨22,_⟩ => (284580371 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284961723 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (35667833 / 125000000 : ℝ)
  | ⟨25,_⟩ => (285722243 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143050709 / 500000000 : ℝ)
  | ⟨27,_⟩ => (143239597 / 500000000 : ℝ)
  | ⟨28,_⟩ => (143428037 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287232059 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287606651 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143990429 / 500000000 : ℝ)
  | ⟨32,_⟩ => (57670837 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288726123 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (57819437 / 200000000 : ℝ)
  | ⟨35,_⟩ => (18091711 / 62500000 : ℝ)
  | ⟨36,_⟩ => (289836691 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290205147 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145286369 / 500000000 : ℝ)
  | ⟨39,_⟩ => (72734739 / 250000000 : ℝ)
  | ⟨40,_⟩ => (291304317 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145834413 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292032483 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12319Cell0 :
    0 ≤ cap12319 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨0,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12319 ⟨0,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨0,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell1 :
    0 ≤ cap12319 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨1,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12319 ⟨1,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨1,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell2 :
    0 ≤ cap12319 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨2,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12319 ⟨2,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨2,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell3 :
    0 ≤ cap12319 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨3,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12319 ⟨3,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨3,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell4 :
    0 ≤ cap12319 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨4,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12319 ⟨4,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨4,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell5 :
    0 ≤ cap12319 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨5,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12319 ⟨5,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨5,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell6 :
    0 ≤ cap12319 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨6,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12319 ⟨6,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨6,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell7 :
    0 ≤ cap12319 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨7,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12319 ⟨7,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨7,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell8 :
    0 ≤ cap12319 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨8,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12319 ⟨8,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨8,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell9 :
    0 ≤ cap12319 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨9,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12319 ⟨9,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨9,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell10 :
    0 ≤ cap12319 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨10,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12319 ⟨10,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨10,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell11 :
    0 ≤ cap12319 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨11,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12319 ⟨11,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨11,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell12 :
    0 ≤ cap12319 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨12,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12319 ⟨12,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨12,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell13 :
    0 ≤ cap12319 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨13,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12319 ⟨13,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨13,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell14 :
    0 ≤ cap12319 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨14,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12319 ⟨14,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨14,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell15 :
    0 ≤ cap12319 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨15,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12319 ⟨15,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨15,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell16 :
    0 ≤ cap12319 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨16,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12319 ⟨16,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨16,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell17 :
    0 ≤ cap12319 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨17,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12319 ⟨17,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨17,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell18 :
    0 ≤ cap12319 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨18,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12319 ⟨18,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨18,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell19 :
    0 ≤ cap12319 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨19,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12319 ⟨19,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨19,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell20 :
    0 ≤ cap12319 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨20,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12319 ⟨20,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨20,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell21 :
    0 ≤ cap12319 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨21,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12319 ⟨21,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨21,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell22 :
    0 ≤ cap12319 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨22,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12319 ⟨22,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨22,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell23 :
    0 ≤ cap12319 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨23,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12319 ⟨23,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨23,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell24 :
    0 ≤ cap12319 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨24,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12319 ⟨24,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨24,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell25 :
    0 ≤ cap12319 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨25,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12319 ⟨25,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨25,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell26 :
    0 ≤ cap12319 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨26,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12319 ⟨26,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨26,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell27 :
    0 ≤ cap12319 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨27,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12319 ⟨27,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨27,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell28 :
    0 ≤ cap12319 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨28,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12319 ⟨28,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨28,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell29 :
    0 ≤ cap12319 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨29,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12319 ⟨29,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨29,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell30 :
    0 ≤ cap12319 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨30,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12319 ⟨30,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨30,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell31 :
    0 ≤ cap12319 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨31,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12319 ⟨31,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨31,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell32 :
    0 ≤ cap12319 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨32,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12319 ⟨32,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨32,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell33 :
    0 ≤ cap12319 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨33,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12319 ⟨33,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨33,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell34 :
    0 ≤ cap12319 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨34,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12319 ⟨34,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨34,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell35 :
    0 ≤ cap12319 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨35,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12319 ⟨35,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨35,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell36 :
    0 ≤ cap12319 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨36,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12319 ⟨36,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨36,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell37 :
    0 ≤ cap12319 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨37,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12319 ⟨37,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨37,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell38 :
    0 ≤ cap12319 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨38,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12319 ⟨38,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨38,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell39 :
    0 ≤ cap12319 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨39,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12319 ⟨39,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨39,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell40 :
    0 ≤ cap12319 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨40,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12319 ⟨40,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨40,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell41 :
    0 ≤ cap12319 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨41,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12319 ⟨41,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨41,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cell42 :
    0 ≤ cap12319 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12319 (parameters ⟨42,by decide⟩)
      (scalarRow12319.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12319 ⟨42,by decide⟩ ∧
    (scalarRow12319.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 ⟨42,by decide⟩ + (scalarRow12319.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12319.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12319.targetFrame := by
  norm_num [cap12319, scalarRow12319, sourceIndex, cell12319, BstLean.Part263.envelope, parameters]

theorem repair12319Cells (j : Fin 43) :
    0 ≤ cap12319 j ∧
    BstLean.Part263.envelope 12319 (parameters j) (scalarRow12319.table (sourceIndex j)).upper ≤ cap12319 j ∧
    (scalarRow12319.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12319 j + (scalarRow12319.table (sourceIndex j)).centre) /
      (scalarRow12319.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12319.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12319Cell0
  | ⟨1,_⟩ => exact repair12319Cell1
  | ⟨2,_⟩ => exact repair12319Cell2
  | ⟨3,_⟩ => exact repair12319Cell3
  | ⟨4,_⟩ => exact repair12319Cell4
  | ⟨5,_⟩ => exact repair12319Cell5
  | ⟨6,_⟩ => exact repair12319Cell6
  | ⟨7,_⟩ => exact repair12319Cell7
  | ⟨8,_⟩ => exact repair12319Cell8
  | ⟨9,_⟩ => exact repair12319Cell9
  | ⟨10,_⟩ => exact repair12319Cell10
  | ⟨11,_⟩ => exact repair12319Cell11
  | ⟨12,_⟩ => exact repair12319Cell12
  | ⟨13,_⟩ => exact repair12319Cell13
  | ⟨14,_⟩ => exact repair12319Cell14
  | ⟨15,_⟩ => exact repair12319Cell15
  | ⟨16,_⟩ => exact repair12319Cell16
  | ⟨17,_⟩ => exact repair12319Cell17
  | ⟨18,_⟩ => exact repair12319Cell18
  | ⟨19,_⟩ => exact repair12319Cell19
  | ⟨20,_⟩ => exact repair12319Cell20
  | ⟨21,_⟩ => exact repair12319Cell21
  | ⟨22,_⟩ => exact repair12319Cell22
  | ⟨23,_⟩ => exact repair12319Cell23
  | ⟨24,_⟩ => exact repair12319Cell24
  | ⟨25,_⟩ => exact repair12319Cell25
  | ⟨26,_⟩ => exact repair12319Cell26
  | ⟨27,_⟩ => exact repair12319Cell27
  | ⟨28,_⟩ => exact repair12319Cell28
  | ⟨29,_⟩ => exact repair12319Cell29
  | ⟨30,_⟩ => exact repair12319Cell30
  | ⟨31,_⟩ => exact repair12319Cell31
  | ⟨32,_⟩ => exact repair12319Cell32
  | ⟨33,_⟩ => exact repair12319Cell33
  | ⟨34,_⟩ => exact repair12319Cell34
  | ⟨35,_⟩ => exact repair12319Cell35
  | ⟨36,_⟩ => exact repair12319Cell36
  | ⟨37,_⟩ => exact repair12319Cell37
  | ⟨38,_⟩ => exact repair12319Cell38
  | ⟨39,_⟩ => exact repair12319Cell39
  | ⟨40,_⟩ => exact repair12319Cell40
  | ⟨41,_⟩ => exact repair12319Cell41
  | ⟨42,_⟩ => exact repair12319Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12319 : FrameRepair 12319 scalarRow12319 where
  cap := cap12319
  cap_nonneg := fun j => (repair12319Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12319])
  endpoint := fun j => (repair12319Cells j).2.1
  endpoint_upper := fun j => (repair12319Cells j).2.2.1
  frame := fun j => (repair12319Cells j).2.2.2

noncomputable def cap12320 : Fin 43 → ℝ
  | ⟨0,_⟩ => (17246597 / 62500000 : ℝ)
  | ⟨1,_⟩ => (17271763 / 62500000 : ℝ)
  | ⟨2,_⟩ => (27674987 / 100000000 : ℝ)
  | ⟨3,_⟩ => (138575267 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277550209 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138974447 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278346119 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139371419 / 500000000 : ℝ)
  | ⟨8,_⟩ => (139569291 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279533353 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (55985431 / 200000000 : ℝ)
  | ⟨11,_⟩ => (70079877 / 250000000 : ℝ)
  | ⟨12,_⟩ => (35088923 / 125000000 : ℝ)
  | ⟨13,_⟩ => (281101813 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (17593261 / 62500000 : ℝ)
  | ⟨15,_⟩ => (281881439 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (882093 / 3125000 : ℝ)
  | ⟨17,_⟩ => (5653143 / 20000000 : ℝ)
  | ⟨18,_⟩ => (283043601 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (70857281 / 250000000 : ℝ)
  | ⟨20,_⟩ => (7095343 / 25000000 : ℝ)
  | ⟨21,_⟩ => (1420987 / 5000000 : ℝ)
  | ⟨22,_⟩ => (284580157 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284961503 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285342437 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285722011 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (14305059 / 50000000 : ℝ)
  | ⟨27,_⟩ => (5729579 / 20000000 : ℝ)
  | ⟨28,_⟩ => (17928489 / 62500000 : ℝ)
  | ⟨29,_⟩ => (143615901 / 500000000 : ℝ)
  | ⟨30,_⟩ => (71901597 / 250000000 : ℝ)
  | ⟨31,_⟩ => (287980589 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (28835391 / 100000000 : ℝ)
  | ⟨33,_⟩ => (144362921 / 500000000 : ℝ)
  | ⟨34,_⟩ => (144548449 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289467083 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (36229549 / 125000000 : ℝ)
  | ⟨37,_⟩ => (145102421 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290572427 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290938639 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145651997 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291668497 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292032149 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12320Cell0 :
    0 ≤ cap12320 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨0,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12320 ⟨0,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨0,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell1 :
    0 ≤ cap12320 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨1,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12320 ⟨1,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨1,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell2 :
    0 ≤ cap12320 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨2,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12320 ⟨2,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨2,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell3 :
    0 ≤ cap12320 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨3,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12320 ⟨3,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨3,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell4 :
    0 ≤ cap12320 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨4,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12320 ⟨4,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨4,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell5 :
    0 ≤ cap12320 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨5,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12320 ⟨5,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨5,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell6 :
    0 ≤ cap12320 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨6,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12320 ⟨6,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨6,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell7 :
    0 ≤ cap12320 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨7,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12320 ⟨7,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨7,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell8 :
    0 ≤ cap12320 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨8,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12320 ⟨8,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨8,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell9 :
    0 ≤ cap12320 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨9,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12320 ⟨9,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨9,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell10 :
    0 ≤ cap12320 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨10,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12320 ⟨10,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨10,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell11 :
    0 ≤ cap12320 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨11,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12320 ⟨11,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨11,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell12 :
    0 ≤ cap12320 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨12,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12320 ⟨12,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨12,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell13 :
    0 ≤ cap12320 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨13,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12320 ⟨13,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨13,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell14 :
    0 ≤ cap12320 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨14,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12320 ⟨14,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨14,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell15 :
    0 ≤ cap12320 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨15,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12320 ⟨15,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨15,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell16 :
    0 ≤ cap12320 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨16,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12320 ⟨16,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨16,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell17 :
    0 ≤ cap12320 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨17,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12320 ⟨17,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨17,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell18 :
    0 ≤ cap12320 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨18,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12320 ⟨18,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨18,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell19 :
    0 ≤ cap12320 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨19,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12320 ⟨19,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨19,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell20 :
    0 ≤ cap12320 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨20,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12320 ⟨20,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨20,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell21 :
    0 ≤ cap12320 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨21,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12320 ⟨21,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨21,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell22 :
    0 ≤ cap12320 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨22,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12320 ⟨22,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨22,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell23 :
    0 ≤ cap12320 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨23,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12320 ⟨23,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨23,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell24 :
    0 ≤ cap12320 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨24,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12320 ⟨24,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨24,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell25 :
    0 ≤ cap12320 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨25,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12320 ⟨25,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨25,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell26 :
    0 ≤ cap12320 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨26,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12320 ⟨26,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨26,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell27 :
    0 ≤ cap12320 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨27,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12320 ⟨27,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨27,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell28 :
    0 ≤ cap12320 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨28,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12320 ⟨28,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨28,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell29 :
    0 ≤ cap12320 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨29,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12320 ⟨29,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨29,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell30 :
    0 ≤ cap12320 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨30,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12320 ⟨30,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨30,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell31 :
    0 ≤ cap12320 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨31,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12320 ⟨31,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨31,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell32 :
    0 ≤ cap12320 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨32,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12320 ⟨32,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨32,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell33 :
    0 ≤ cap12320 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨33,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12320 ⟨33,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨33,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell34 :
    0 ≤ cap12320 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨34,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12320 ⟨34,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨34,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell35 :
    0 ≤ cap12320 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨35,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12320 ⟨35,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨35,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell36 :
    0 ≤ cap12320 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨36,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12320 ⟨36,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨36,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell37 :
    0 ≤ cap12320 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨37,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12320 ⟨37,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨37,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell38 :
    0 ≤ cap12320 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨38,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12320 ⟨38,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨38,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell39 :
    0 ≤ cap12320 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨39,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12320 ⟨39,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨39,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell40 :
    0 ≤ cap12320 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨40,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12320 ⟨40,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨40,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell41 :
    0 ≤ cap12320 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨41,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12320 ⟨41,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨41,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cell42 :
    0 ≤ cap12320 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12320 (parameters ⟨42,by decide⟩)
      (scalarRow12320.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12320 ⟨42,by decide⟩ ∧
    (scalarRow12320.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 ⟨42,by decide⟩ + (scalarRow12320.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12320.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12320.targetFrame := by
  norm_num [cap12320, scalarRow12320, sourceIndex, cell12320, BstLean.Part263.envelope, parameters]

theorem repair12320Cells (j : Fin 43) :
    0 ≤ cap12320 j ∧
    BstLean.Part263.envelope 12320 (parameters j) (scalarRow12320.table (sourceIndex j)).upper ≤ cap12320 j ∧
    (scalarRow12320.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12320 j + (scalarRow12320.table (sourceIndex j)).centre) /
      (scalarRow12320.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12320.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12320Cell0
  | ⟨1,_⟩ => exact repair12320Cell1
  | ⟨2,_⟩ => exact repair12320Cell2
  | ⟨3,_⟩ => exact repair12320Cell3
  | ⟨4,_⟩ => exact repair12320Cell4
  | ⟨5,_⟩ => exact repair12320Cell5
  | ⟨6,_⟩ => exact repair12320Cell6
  | ⟨7,_⟩ => exact repair12320Cell7
  | ⟨8,_⟩ => exact repair12320Cell8
  | ⟨9,_⟩ => exact repair12320Cell9
  | ⟨10,_⟩ => exact repair12320Cell10
  | ⟨11,_⟩ => exact repair12320Cell11
  | ⟨12,_⟩ => exact repair12320Cell12
  | ⟨13,_⟩ => exact repair12320Cell13
  | ⟨14,_⟩ => exact repair12320Cell14
  | ⟨15,_⟩ => exact repair12320Cell15
  | ⟨16,_⟩ => exact repair12320Cell16
  | ⟨17,_⟩ => exact repair12320Cell17
  | ⟨18,_⟩ => exact repair12320Cell18
  | ⟨19,_⟩ => exact repair12320Cell19
  | ⟨20,_⟩ => exact repair12320Cell20
  | ⟨21,_⟩ => exact repair12320Cell21
  | ⟨22,_⟩ => exact repair12320Cell22
  | ⟨23,_⟩ => exact repair12320Cell23
  | ⟨24,_⟩ => exact repair12320Cell24
  | ⟨25,_⟩ => exact repair12320Cell25
  | ⟨26,_⟩ => exact repair12320Cell26
  | ⟨27,_⟩ => exact repair12320Cell27
  | ⟨28,_⟩ => exact repair12320Cell28
  | ⟨29,_⟩ => exact repair12320Cell29
  | ⟨30,_⟩ => exact repair12320Cell30
  | ⟨31,_⟩ => exact repair12320Cell31
  | ⟨32,_⟩ => exact repair12320Cell32
  | ⟨33,_⟩ => exact repair12320Cell33
  | ⟨34,_⟩ => exact repair12320Cell34
  | ⟨35,_⟩ => exact repair12320Cell35
  | ⟨36,_⟩ => exact repair12320Cell36
  | ⟨37,_⟩ => exact repair12320Cell37
  | ⟨38,_⟩ => exact repair12320Cell38
  | ⟨39,_⟩ => exact repair12320Cell39
  | ⟨40,_⟩ => exact repair12320Cell40
  | ⟨41,_⟩ => exact repair12320Cell41
  | ⟨42,_⟩ => exact repair12320Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12320 : FrameRepair 12320 scalarRow12320 where
  cap := cap12320
  cap_nonneg := fun j => (repair12320Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12320])
  endpoint := fun j => (repair12320Cells j).2.1
  endpoint_upper := fun j => (repair12320Cells j).2.2.1
  frame := fun j => (repair12320Cells j).2.2.2

noncomputable def cap12321 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275945477 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138174063 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138374891 / 500000000 : ℝ)
  | ⟨3,_⟩ => (6928761 / 25000000 : ℝ)
  | ⟨4,_⟩ => (69387527 / 250000000 : ℝ)
  | ⟨5,_⟩ => (277948787 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55669201 / 200000000 : ℝ)
  | ⟨7,_⟩ => (139371359 / 500000000 : ℝ)
  | ⟨8,_⟩ => (55827691 / 200000000 : ℝ)
  | ⟨9,_⟩ => (279533221 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (34990877 / 125000000 : ℝ)
  | ⟨11,_⟩ => (140159681 / 500000000 : ℝ)
  | ⟨12,_⟩ => (4386113 / 15625000 : ℝ)
  | ⟨13,_⟩ => (56220331 / 200000000 : ℝ)
  | ⟨14,_⟩ => (70373003 / 250000000 : ℝ)
  | ⟨15,_⟩ => (281881269 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282269583 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282656967 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (70760853 / 250000000 : ℝ)
  | ⟨19,_⟩ => (283428929 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283813519 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284197193 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284579943 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284961283 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285342211 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142860889 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286100941 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (57295741 / 200000000 : ℝ)
  | ⟨28,_⟩ => (286855573 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143615773 / 500000000 : ℝ)
  | ⟨30,_⟩ => (2300849 / 8000000 : ℝ)
  | ⟨31,_⟩ => (287980321 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (57670727 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288725561 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289096611 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (28946679 / 100000000 : ℝ)
  | ⟨36,_⟩ => (289836093 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290204537 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (72643029 / 250000000 : ℝ)
  | ⟨39,_⟩ => (290938323 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291303671 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (36458521 / 125000000 : ℝ)
  | ⟨42,_⟩ => (146015907 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12321Cell0 :
    0 ≤ cap12321 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨0,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12321 ⟨0,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨0,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell1 :
    0 ≤ cap12321 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨1,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12321 ⟨1,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨1,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell2 :
    0 ≤ cap12321 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨2,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12321 ⟨2,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨2,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell3 :
    0 ≤ cap12321 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨3,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12321 ⟨3,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨3,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell4 :
    0 ≤ cap12321 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨4,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12321 ⟨4,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨4,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell5 :
    0 ≤ cap12321 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨5,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12321 ⟨5,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨5,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell6 :
    0 ≤ cap12321 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨6,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12321 ⟨6,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨6,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell7 :
    0 ≤ cap12321 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨7,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12321 ⟨7,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨7,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell8 :
    0 ≤ cap12321 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨8,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12321 ⟨8,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨8,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell9 :
    0 ≤ cap12321 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨9,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12321 ⟨9,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨9,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell10 :
    0 ≤ cap12321 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨10,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12321 ⟨10,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨10,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell11 :
    0 ≤ cap12321 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨11,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12321 ⟨11,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨11,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell12 :
    0 ≤ cap12321 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨12,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12321 ⟨12,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨12,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell13 :
    0 ≤ cap12321 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨13,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12321 ⟨13,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨13,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell14 :
    0 ≤ cap12321 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨14,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12321 ⟨14,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨14,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell15 :
    0 ≤ cap12321 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨15,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12321 ⟨15,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨15,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell16 :
    0 ≤ cap12321 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨16,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12321 ⟨16,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨16,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell17 :
    0 ≤ cap12321 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨17,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12321 ⟨17,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨17,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell18 :
    0 ≤ cap12321 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨18,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12321 ⟨18,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨18,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell19 :
    0 ≤ cap12321 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨19,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12321 ⟨19,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨19,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell20 :
    0 ≤ cap12321 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨20,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12321 ⟨20,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨20,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell21 :
    0 ≤ cap12321 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨21,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12321 ⟨21,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨21,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell22 :
    0 ≤ cap12321 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨22,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12321 ⟨22,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨22,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell23 :
    0 ≤ cap12321 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨23,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12321 ⟨23,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨23,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell24 :
    0 ≤ cap12321 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨24,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12321 ⟨24,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨24,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell25 :
    0 ≤ cap12321 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨25,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12321 ⟨25,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨25,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell26 :
    0 ≤ cap12321 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨26,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12321 ⟨26,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨26,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell27 :
    0 ≤ cap12321 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨27,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12321 ⟨27,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨27,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell28 :
    0 ≤ cap12321 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨28,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12321 ⟨28,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨28,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell29 :
    0 ≤ cap12321 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨29,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12321 ⟨29,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨29,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell30 :
    0 ≤ cap12321 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨30,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12321 ⟨30,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨30,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell31 :
    0 ≤ cap12321 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨31,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12321 ⟨31,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨31,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell32 :
    0 ≤ cap12321 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨32,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12321 ⟨32,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨32,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell33 :
    0 ≤ cap12321 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨33,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12321 ⟨33,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨33,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell34 :
    0 ≤ cap12321 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨34,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12321 ⟨34,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨34,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell35 :
    0 ≤ cap12321 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨35,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12321 ⟨35,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨35,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell36 :
    0 ≤ cap12321 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨36,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12321 ⟨36,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨36,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell37 :
    0 ≤ cap12321 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨37,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12321 ⟨37,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨37,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell38 :
    0 ≤ cap12321 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨38,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12321 ⟨38,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨38,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell39 :
    0 ≤ cap12321 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨39,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12321 ⟨39,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨39,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell40 :
    0 ≤ cap12321 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨40,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12321 ⟨40,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨40,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell41 :
    0 ≤ cap12321 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨41,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12321 ⟨41,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨41,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cell42 :
    0 ≤ cap12321 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12321 (parameters ⟨42,by decide⟩)
      (scalarRow12321.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12321 ⟨42,by decide⟩ ∧
    (scalarRow12321.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 ⟨42,by decide⟩ + (scalarRow12321.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12321.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12321.targetFrame := by
  norm_num [cap12321, scalarRow12321, sourceIndex, cell12321, BstLean.Part263.envelope, parameters]

theorem repair12321Cells (j : Fin 43) :
    0 ≤ cap12321 j ∧
    BstLean.Part263.envelope 12321 (parameters j) (scalarRow12321.table (sourceIndex j)).upper ≤ cap12321 j ∧
    (scalarRow12321.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12321 j + (scalarRow12321.table (sourceIndex j)).centre) /
      (scalarRow12321.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12321.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12321Cell0
  | ⟨1,_⟩ => exact repair12321Cell1
  | ⟨2,_⟩ => exact repair12321Cell2
  | ⟨3,_⟩ => exact repair12321Cell3
  | ⟨4,_⟩ => exact repair12321Cell4
  | ⟨5,_⟩ => exact repair12321Cell5
  | ⟨6,_⟩ => exact repair12321Cell6
  | ⟨7,_⟩ => exact repair12321Cell7
  | ⟨8,_⟩ => exact repair12321Cell8
  | ⟨9,_⟩ => exact repair12321Cell9
  | ⟨10,_⟩ => exact repair12321Cell10
  | ⟨11,_⟩ => exact repair12321Cell11
  | ⟨12,_⟩ => exact repair12321Cell12
  | ⟨13,_⟩ => exact repair12321Cell13
  | ⟨14,_⟩ => exact repair12321Cell14
  | ⟨15,_⟩ => exact repair12321Cell15
  | ⟨16,_⟩ => exact repair12321Cell16
  | ⟨17,_⟩ => exact repair12321Cell17
  | ⟨18,_⟩ => exact repair12321Cell18
  | ⟨19,_⟩ => exact repair12321Cell19
  | ⟨20,_⟩ => exact repair12321Cell20
  | ⟨21,_⟩ => exact repair12321Cell21
  | ⟨22,_⟩ => exact repair12321Cell22
  | ⟨23,_⟩ => exact repair12321Cell23
  | ⟨24,_⟩ => exact repair12321Cell24
  | ⟨25,_⟩ => exact repair12321Cell25
  | ⟨26,_⟩ => exact repair12321Cell26
  | ⟨27,_⟩ => exact repair12321Cell27
  | ⟨28,_⟩ => exact repair12321Cell28
  | ⟨29,_⟩ => exact repair12321Cell29
  | ⟨30,_⟩ => exact repair12321Cell30
  | ⟨31,_⟩ => exact repair12321Cell31
  | ⟨32,_⟩ => exact repair12321Cell32
  | ⟨33,_⟩ => exact repair12321Cell33
  | ⟨34,_⟩ => exact repair12321Cell34
  | ⟨35,_⟩ => exact repair12321Cell35
  | ⟨36,_⟩ => exact repair12321Cell36
  | ⟨37,_⟩ => exact repair12321Cell37
  | ⟨38,_⟩ => exact repair12321Cell38
  | ⟨39,_⟩ => exact repair12321Cell39
  | ⟨40,_⟩ => exact repair12321Cell40
  | ⟨41,_⟩ => exact repair12321Cell41
  | ⟨42,_⟩ => exact repair12321Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12321 : FrameRepair 12321 scalarRow12321 where
  cap := cap12321
  cap_nonneg := fun j => (repair12321Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12321])
  endpoint := fun j => (repair12321Cells j).2.1
  endpoint_upper := fun j => (repair12321Cells j).2.2.1
  frame := fun j => (repair12321Cells j).2.2.2

noncomputable def cap12322 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137972701 / 500000000 : ℝ)
  | ⟨1,_⟩ => (55269609 / 200000000 : ℝ)
  | ⟨2,_⟩ => (138374847 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138575173 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277550007 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (6948717 / 25000000 : ℝ)
  | ⟨6,_⟩ => (69586473 / 250000000 : ℝ)
  | ⟨7,_⟩ => (139371299 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279138329 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (8735409 / 31250000 : ℝ)
  | ⟨10,_⟩ => (69981719 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280319217 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (7017777 / 25000000 : ℝ)
  | ⟨13,_⟩ => (281101497 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281491847 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140940549 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282269407 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (17666049 / 62500000 : ℝ)
  | ⟨18,_⟩ => (283043223 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283428733 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283813317 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56839397 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284579729 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284961063 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (57068397 / 200000000 : ℝ)
  | ⟨25,_⟩ => (142860773 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286100703 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286478461 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143427661 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287231289 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143802931 / 500000000 : ℝ)
  | ⟨31,_⟩ => (71995013 / 250000000 : ℝ)
  | ⟨32,_⟩ => (288353361 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (1804533 / 6250000 : ℝ)
  | ⟨34,_⟩ => (72274081 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289466497 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144917897 / 500000000 : ℝ)
  | ⟨37,_⟩ => (36275529 / 125000000 : ℝ)
  | ⟨38,_⟩ => (58114361 / 200000000 : ℝ)
  | ⟨39,_⟩ => (145469003 / 500000000 : ℝ)
  | ⟨40,_⟩ => (72825837 / 250000000 : ℝ)
  | ⟨41,_⟩ => (455731 / 1562500 : ℝ)
  | ⟨42,_⟩ => (7300787 / 25000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12322Cell0 :
    0 ≤ cap12322 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨0,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12322 ⟨0,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨0,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell1 :
    0 ≤ cap12322 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨1,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12322 ⟨1,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨1,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell2 :
    0 ≤ cap12322 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨2,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12322 ⟨2,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨2,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell3 :
    0 ≤ cap12322 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨3,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12322 ⟨3,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨3,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell4 :
    0 ≤ cap12322 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨4,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12322 ⟨4,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨4,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell5 :
    0 ≤ cap12322 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨5,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12322 ⟨5,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨5,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell6 :
    0 ≤ cap12322 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨6,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12322 ⟨6,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨6,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell7 :
    0 ≤ cap12322 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨7,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12322 ⟨7,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨7,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell8 :
    0 ≤ cap12322 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨8,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12322 ⟨8,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨8,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell9 :
    0 ≤ cap12322 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨9,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12322 ⟨9,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨9,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell10 :
    0 ≤ cap12322 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨10,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12322 ⟨10,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨10,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell11 :
    0 ≤ cap12322 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨11,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12322 ⟨11,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨11,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell12 :
    0 ≤ cap12322 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨12,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12322 ⟨12,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨12,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell13 :
    0 ≤ cap12322 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨13,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12322 ⟨13,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨13,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell14 :
    0 ≤ cap12322 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨14,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12322 ⟨14,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨14,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell15 :
    0 ≤ cap12322 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨15,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12322 ⟨15,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨15,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell16 :
    0 ≤ cap12322 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨16,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12322 ⟨16,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨16,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell17 :
    0 ≤ cap12322 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨17,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12322 ⟨17,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨17,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell18 :
    0 ≤ cap12322 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨18,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12322 ⟨18,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨18,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell19 :
    0 ≤ cap12322 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨19,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12322 ⟨19,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨19,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell20 :
    0 ≤ cap12322 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨20,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12322 ⟨20,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨20,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell21 :
    0 ≤ cap12322 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨21,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12322 ⟨21,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨21,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell22 :
    0 ≤ cap12322 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨22,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12322 ⟨22,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨22,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell23 :
    0 ≤ cap12322 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨23,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12322 ⟨23,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨23,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell24 :
    0 ≤ cap12322 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨24,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12322 ⟨24,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨24,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell25 :
    0 ≤ cap12322 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨25,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12322 ⟨25,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨25,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell26 :
    0 ≤ cap12322 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨26,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12322 ⟨26,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨26,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell27 :
    0 ≤ cap12322 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨27,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12322 ⟨27,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨27,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell28 :
    0 ≤ cap12322 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨28,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12322 ⟨28,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨28,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell29 :
    0 ≤ cap12322 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨29,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12322 ⟨29,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨29,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell30 :
    0 ≤ cap12322 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨30,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12322 ⟨30,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨30,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell31 :
    0 ≤ cap12322 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨31,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12322 ⟨31,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨31,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell32 :
    0 ≤ cap12322 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨32,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12322 ⟨32,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨32,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell33 :
    0 ≤ cap12322 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨33,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12322 ⟨33,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨33,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell34 :
    0 ≤ cap12322 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨34,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12322 ⟨34,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨34,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell35 :
    0 ≤ cap12322 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨35,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12322 ⟨35,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨35,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell36 :
    0 ≤ cap12322 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨36,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12322 ⟨36,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨36,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell37 :
    0 ≤ cap12322 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨37,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12322 ⟨37,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨37,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell38 :
    0 ≤ cap12322 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨38,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12322 ⟨38,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨38,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell39 :
    0 ≤ cap12322 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨39,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12322 ⟨39,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨39,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell40 :
    0 ≤ cap12322 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨40,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12322 ⟨40,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨40,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell41 :
    0 ≤ cap12322 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨41,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12322 ⟨41,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨41,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cell42 :
    0 ≤ cap12322 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12322 (parameters ⟨42,by decide⟩)
      (scalarRow12322.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12322 ⟨42,by decide⟩ ∧
    (scalarRow12322.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 ⟨42,by decide⟩ + (scalarRow12322.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12322.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12322.targetFrame := by
  norm_num [cap12322, scalarRow12322, sourceIndex, cell12322, BstLean.Part263.envelope, parameters]

theorem repair12322Cells (j : Fin 43) :
    0 ≤ cap12322 j ∧
    BstLean.Part263.envelope 12322 (parameters j) (scalarRow12322.table (sourceIndex j)).upper ≤ cap12322 j ∧
    (scalarRow12322.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12322 j + (scalarRow12322.table (sourceIndex j)).centre) /
      (scalarRow12322.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12322.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12322Cell0
  | ⟨1,_⟩ => exact repair12322Cell1
  | ⟨2,_⟩ => exact repair12322Cell2
  | ⟨3,_⟩ => exact repair12322Cell3
  | ⟨4,_⟩ => exact repair12322Cell4
  | ⟨5,_⟩ => exact repair12322Cell5
  | ⟨6,_⟩ => exact repair12322Cell6
  | ⟨7,_⟩ => exact repair12322Cell7
  | ⟨8,_⟩ => exact repair12322Cell8
  | ⟨9,_⟩ => exact repair12322Cell9
  | ⟨10,_⟩ => exact repair12322Cell10
  | ⟨11,_⟩ => exact repair12322Cell11
  | ⟨12,_⟩ => exact repair12322Cell12
  | ⟨13,_⟩ => exact repair12322Cell13
  | ⟨14,_⟩ => exact repair12322Cell14
  | ⟨15,_⟩ => exact repair12322Cell15
  | ⟨16,_⟩ => exact repair12322Cell16
  | ⟨17,_⟩ => exact repair12322Cell17
  | ⟨18,_⟩ => exact repair12322Cell18
  | ⟨19,_⟩ => exact repair12322Cell19
  | ⟨20,_⟩ => exact repair12322Cell20
  | ⟨21,_⟩ => exact repair12322Cell21
  | ⟨22,_⟩ => exact repair12322Cell22
  | ⟨23,_⟩ => exact repair12322Cell23
  | ⟨24,_⟩ => exact repair12322Cell24
  | ⟨25,_⟩ => exact repair12322Cell25
  | ⟨26,_⟩ => exact repair12322Cell26
  | ⟨27,_⟩ => exact repair12322Cell27
  | ⟨28,_⟩ => exact repair12322Cell28
  | ⟨29,_⟩ => exact repair12322Cell29
  | ⟨30,_⟩ => exact repair12322Cell30
  | ⟨31,_⟩ => exact repair12322Cell31
  | ⟨32,_⟩ => exact repair12322Cell32
  | ⟨33,_⟩ => exact repair12322Cell33
  | ⟨34,_⟩ => exact repair12322Cell34
  | ⟨35,_⟩ => exact repair12322Cell35
  | ⟨36,_⟩ => exact repair12322Cell36
  | ⟨37,_⟩ => exact repair12322Cell37
  | ⟨38,_⟩ => exact repair12322Cell38
  | ⟨39,_⟩ => exact repair12322Cell39
  | ⟨40,_⟩ => exact repair12322Cell40
  | ⟨41,_⟩ => exact repair12322Cell41
  | ⟨42,_⟩ => exact repair12322Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12322 : FrameRepair 12322 scalarRow12322 where
  cap := cap12322
  cap_nonneg := fun j => (repair12322Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12322])
  endpoint := fun j => (repair12322Cells j).2.1
  endpoint_upper := fun j => (repair12322Cells j).2.2.1
  frame := fun j => (repair12322Cells j).2.2.2

noncomputable def cap12323 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275945327 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276347963 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138374803 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277150251 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277549907 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277948573 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139172889 / 500000000 : ℝ)
  | ⟨7,_⟩ => (139371239 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279138203 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55906591 / 200000000 : ℝ)
  | ⟨10,_⟩ => (139963369 / 500000000 : ℝ)
  | ⟨11,_⟩ => (8759971 / 31250000 : ℝ)
  | ⟨12,_⟩ => (280710929 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281101339 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281491683 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (8808779 / 31250000 : ℝ)
  | ⟨16,_⟩ => (28226923 / 100000000 : ℝ)
  | ⟨17,_⟩ => (282656601 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141521517 / 500000000 : ℝ)
  | ⟨19,_⟩ => (141714269 / 500000000 : ℝ)
  | ⟨20,_⟩ => (70953279 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284196777 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (56915903 / 200000000 : ℝ)
  | ⟨23,_⟩ => (284960843 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285341759 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285721313 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (17881279 / 62500000 : ℝ)
  | ⟨27,_⟩ => (35809777 / 125000000 : ℝ)
  | ⟨28,_⟩ => (8964221 / 31250000 : ℝ)
  | ⟨29,_⟩ => (35903879 / 125000000 : ℝ)
  | ⟨30,_⟩ => (359507 / 1250000 : ℝ)
  | ⟨31,_⟩ => (287979783 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (144176543 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288724999 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289096037 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72366551 / 250000000 : ℝ)
  | ⟨36,_⟩ => (57967099 / 200000000 : ℝ)
  | ⟨37,_⟩ => (290203927 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145285747 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290937689 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (145651513 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291667511 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (58406229 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12323Cell0 :
    0 ≤ cap12323 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨0,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12323 ⟨0,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨0,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell1 :
    0 ≤ cap12323 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨1,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12323 ⟨1,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨1,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell2 :
    0 ≤ cap12323 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨2,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12323 ⟨2,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨2,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell3 :
    0 ≤ cap12323 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨3,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12323 ⟨3,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨3,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell4 :
    0 ≤ cap12323 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨4,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12323 ⟨4,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨4,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell5 :
    0 ≤ cap12323 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨5,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12323 ⟨5,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨5,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell6 :
    0 ≤ cap12323 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨6,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12323 ⟨6,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨6,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell7 :
    0 ≤ cap12323 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨7,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12323 ⟨7,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨7,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell8 :
    0 ≤ cap12323 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨8,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12323 ⟨8,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨8,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell9 :
    0 ≤ cap12323 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨9,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12323 ⟨9,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨9,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell10 :
    0 ≤ cap12323 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨10,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12323 ⟨10,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨10,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell11 :
    0 ≤ cap12323 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨11,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12323 ⟨11,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨11,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell12 :
    0 ≤ cap12323 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨12,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12323 ⟨12,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨12,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell13 :
    0 ≤ cap12323 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨13,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12323 ⟨13,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨13,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell14 :
    0 ≤ cap12323 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨14,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12323 ⟨14,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨14,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell15 :
    0 ≤ cap12323 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨15,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12323 ⟨15,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨15,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell16 :
    0 ≤ cap12323 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨16,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12323 ⟨16,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨16,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell17 :
    0 ≤ cap12323 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨17,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12323 ⟨17,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨17,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell18 :
    0 ≤ cap12323 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨18,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12323 ⟨18,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨18,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell19 :
    0 ≤ cap12323 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨19,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12323 ⟨19,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨19,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell20 :
    0 ≤ cap12323 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨20,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12323 ⟨20,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨20,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell21 :
    0 ≤ cap12323 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨21,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12323 ⟨21,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨21,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell22 :
    0 ≤ cap12323 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨22,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12323 ⟨22,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨22,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell23 :
    0 ≤ cap12323 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨23,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12323 ⟨23,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨23,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell24 :
    0 ≤ cap12323 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨24,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12323 ⟨24,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨24,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell25 :
    0 ≤ cap12323 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨25,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12323 ⟨25,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨25,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell26 :
    0 ≤ cap12323 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨26,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12323 ⟨26,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨26,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell27 :
    0 ≤ cap12323 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨27,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12323 ⟨27,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨27,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell28 :
    0 ≤ cap12323 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨28,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12323 ⟨28,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨28,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell29 :
    0 ≤ cap12323 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨29,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12323 ⟨29,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨29,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell30 :
    0 ≤ cap12323 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨30,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12323 ⟨30,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨30,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell31 :
    0 ≤ cap12323 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨31,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12323 ⟨31,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨31,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell32 :
    0 ≤ cap12323 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨32,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12323 ⟨32,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨32,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell33 :
    0 ≤ cap12323 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨33,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12323 ⟨33,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨33,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell34 :
    0 ≤ cap12323 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨34,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12323 ⟨34,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨34,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell35 :
    0 ≤ cap12323 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨35,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12323 ⟨35,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨35,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell36 :
    0 ≤ cap12323 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨36,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12323 ⟨36,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨36,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell37 :
    0 ≤ cap12323 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨37,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12323 ⟨37,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨37,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell38 :
    0 ≤ cap12323 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨38,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12323 ⟨38,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨38,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell39 :
    0 ≤ cap12323 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨39,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12323 ⟨39,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨39,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell40 :
    0 ≤ cap12323 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨40,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12323 ⟨40,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨40,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell41 :
    0 ≤ cap12323 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨41,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12323 ⟨41,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨41,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cell42 :
    0 ≤ cap12323 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12323 (parameters ⟨42,by decide⟩)
      (scalarRow12323.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12323 ⟨42,by decide⟩ ∧
    (scalarRow12323.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 ⟨42,by decide⟩ + (scalarRow12323.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12323.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12323.targetFrame := by
  norm_num [cap12323, scalarRow12323, sourceIndex, cell12323, BstLean.Part263.envelope, parameters]

theorem repair12323Cells (j : Fin 43) :
    0 ≤ cap12323 j ∧
    BstLean.Part263.envelope 12323 (parameters j) (scalarRow12323.table (sourceIndex j)).upper ≤ cap12323 j ∧
    (scalarRow12323.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12323 j + (scalarRow12323.table (sourceIndex j)).centre) /
      (scalarRow12323.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12323.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12323Cell0
  | ⟨1,_⟩ => exact repair12323Cell1
  | ⟨2,_⟩ => exact repair12323Cell2
  | ⟨3,_⟩ => exact repair12323Cell3
  | ⟨4,_⟩ => exact repair12323Cell4
  | ⟨5,_⟩ => exact repair12323Cell5
  | ⟨6,_⟩ => exact repair12323Cell6
  | ⟨7,_⟩ => exact repair12323Cell7
  | ⟨8,_⟩ => exact repair12323Cell8
  | ⟨9,_⟩ => exact repair12323Cell9
  | ⟨10,_⟩ => exact repair12323Cell10
  | ⟨11,_⟩ => exact repair12323Cell11
  | ⟨12,_⟩ => exact repair12323Cell12
  | ⟨13,_⟩ => exact repair12323Cell13
  | ⟨14,_⟩ => exact repair12323Cell14
  | ⟨15,_⟩ => exact repair12323Cell15
  | ⟨16,_⟩ => exact repair12323Cell16
  | ⟨17,_⟩ => exact repair12323Cell17
  | ⟨18,_⟩ => exact repair12323Cell18
  | ⟨19,_⟩ => exact repair12323Cell19
  | ⟨20,_⟩ => exact repair12323Cell20
  | ⟨21,_⟩ => exact repair12323Cell21
  | ⟨22,_⟩ => exact repair12323Cell22
  | ⟨23,_⟩ => exact repair12323Cell23
  | ⟨24,_⟩ => exact repair12323Cell24
  | ⟨25,_⟩ => exact repair12323Cell25
  | ⟨26,_⟩ => exact repair12323Cell26
  | ⟨27,_⟩ => exact repair12323Cell27
  | ⟨28,_⟩ => exact repair12323Cell28
  | ⟨29,_⟩ => exact repair12323Cell29
  | ⟨30,_⟩ => exact repair12323Cell30
  | ⟨31,_⟩ => exact repair12323Cell31
  | ⟨32,_⟩ => exact repair12323Cell32
  | ⟨33,_⟩ => exact repair12323Cell33
  | ⟨34,_⟩ => exact repair12323Cell34
  | ⟨35,_⟩ => exact repair12323Cell35
  | ⟨36,_⟩ => exact repair12323Cell36
  | ⟨37,_⟩ => exact repair12323Cell37
  | ⟨38,_⟩ => exact repair12323Cell38
  | ⟨39,_⟩ => exact repair12323Cell39
  | ⟨40,_⟩ => exact repair12323Cell40
  | ⟨41,_⟩ => exact repair12323Cell41
  | ⟨42,_⟩ => exact repair12323Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12323 : FrameRepair 12323 scalarRow12323 where
  cap := cap12323
  cap_nonneg := fun j => (repair12323Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12323])
  endpoint := fun j => (repair12323Cells j).2.1
  endpoint_upper := fun j => (repair12323Cells j).2.2.1
  frame := fun j => (repair12323Cells j).2.2.2

noncomputable def cap12324 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68986313 / 250000000 : ℝ)
  | ⟨1,_⟩ => (138173941 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138374759 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277150157 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (138774903 / 500000000 : ℝ)
  | ⟨5,_⟩ => (55589693 / 200000000 : ℝ)
  | ⟨6,_⟩ => (55669133 / 200000000 : ℝ)
  | ⟨7,_⟩ => (139371179 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69784519 / 250000000 : ℝ)
  | ⟨9,_⟩ => (279532823 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279926599 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140159463 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280710777 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140550591 / 500000000 : ℝ)
  | ⟨14,_⟩ => (281491519 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281880757 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282269053 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (141328209 / 500000000 : ℝ)
  | ⟨18,_⟩ => (70760711 / 250000000 : ℝ)
  | ⟨19,_⟩ => (283428343 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141906457 / 500000000 : ℝ)
  | ⟨21,_⟩ => (28419657 / 100000000 : ℝ)
  | ⟨22,_⟩ => (142289651 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284960623 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71335383 / 250000000 : ℝ)
  | ⟨25,_⟩ => (285721081 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143050113 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286477971 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286854821 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (35903847 / 125000000 : ℝ)
  | ⟨30,_⟩ => (287605337 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143989757 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288352811 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144362359 / 500000000 : ℝ)
  | ⟨34,_⟩ => (1156383 / 4000000 : ℝ)
  | ⟨35,_⟩ => (289465911 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (72458799 / 250000000 : ℝ)
  | ⟨37,_⟩ => (145101811 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290571183 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (72734343 / 250000000 : ℝ)
  | ⟨40,_⟩ => (291302703 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145833591 / 500000000 : ℝ)
  | ⟨42,_⟩ => (29203081 / 100000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12324Cell0 :
    0 ≤ cap12324 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨0,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12324 ⟨0,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨0,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell1 :
    0 ≤ cap12324 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨1,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12324 ⟨1,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨1,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell2 :
    0 ≤ cap12324 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨2,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12324 ⟨2,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨2,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell3 :
    0 ≤ cap12324 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨3,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12324 ⟨3,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨3,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell4 :
    0 ≤ cap12324 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨4,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12324 ⟨4,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨4,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell5 :
    0 ≤ cap12324 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨5,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12324 ⟨5,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨5,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell6 :
    0 ≤ cap12324 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨6,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12324 ⟨6,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨6,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell7 :
    0 ≤ cap12324 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨7,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12324 ⟨7,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨7,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell8 :
    0 ≤ cap12324 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨8,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12324 ⟨8,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨8,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell9 :
    0 ≤ cap12324 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨9,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12324 ⟨9,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨9,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell10 :
    0 ≤ cap12324 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨10,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12324 ⟨10,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨10,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell11 :
    0 ≤ cap12324 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨11,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12324 ⟨11,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨11,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell12 :
    0 ≤ cap12324 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨12,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12324 ⟨12,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨12,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell13 :
    0 ≤ cap12324 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨13,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12324 ⟨13,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨13,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell14 :
    0 ≤ cap12324 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨14,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12324 ⟨14,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨14,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell15 :
    0 ≤ cap12324 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨15,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12324 ⟨15,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨15,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell16 :
    0 ≤ cap12324 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨16,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12324 ⟨16,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨16,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell17 :
    0 ≤ cap12324 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨17,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12324 ⟨17,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨17,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell18 :
    0 ≤ cap12324 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨18,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12324 ⟨18,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨18,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell19 :
    0 ≤ cap12324 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨19,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12324 ⟨19,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨19,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell20 :
    0 ≤ cap12324 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨20,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12324 ⟨20,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨20,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell21 :
    0 ≤ cap12324 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨21,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12324 ⟨21,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨21,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell22 :
    0 ≤ cap12324 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨22,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12324 ⟨22,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨22,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell23 :
    0 ≤ cap12324 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨23,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12324 ⟨23,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨23,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell24 :
    0 ≤ cap12324 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨24,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12324 ⟨24,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨24,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell25 :
    0 ≤ cap12324 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨25,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12324 ⟨25,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨25,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell26 :
    0 ≤ cap12324 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨26,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12324 ⟨26,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨26,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell27 :
    0 ≤ cap12324 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨27,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12324 ⟨27,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨27,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell28 :
    0 ≤ cap12324 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨28,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12324 ⟨28,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨28,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell29 :
    0 ≤ cap12324 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨29,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12324 ⟨29,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨29,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell30 :
    0 ≤ cap12324 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨30,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12324 ⟨30,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨30,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell31 :
    0 ≤ cap12324 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨31,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12324 ⟨31,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨31,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell32 :
    0 ≤ cap12324 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨32,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12324 ⟨32,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨32,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell33 :
    0 ≤ cap12324 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨33,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12324 ⟨33,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨33,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell34 :
    0 ≤ cap12324 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨34,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12324 ⟨34,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨34,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell35 :
    0 ≤ cap12324 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨35,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12324 ⟨35,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨35,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell36 :
    0 ≤ cap12324 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨36,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12324 ⟨36,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨36,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell37 :
    0 ≤ cap12324 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨37,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12324 ⟨37,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨37,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell38 :
    0 ≤ cap12324 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨38,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12324 ⟨38,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨38,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell39 :
    0 ≤ cap12324 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨39,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12324 ⟨39,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨39,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell40 :
    0 ≤ cap12324 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨40,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12324 ⟨40,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨40,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell41 :
    0 ≤ cap12324 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨41,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12324 ⟨41,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨41,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cell42 :
    0 ≤ cap12324 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12324 (parameters ⟨42,by decide⟩)
      (scalarRow12324.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12324 ⟨42,by decide⟩ ∧
    (scalarRow12324.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 ⟨42,by decide⟩ + (scalarRow12324.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12324.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12324.targetFrame := by
  norm_num [cap12324, scalarRow12324, sourceIndex, cell12324, BstLean.Part263.envelope, parameters]

theorem repair12324Cells (j : Fin 43) :
    0 ≤ cap12324 j ∧
    BstLean.Part263.envelope 12324 (parameters j) (scalarRow12324.table (sourceIndex j)).upper ≤ cap12324 j ∧
    (scalarRow12324.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12324 j + (scalarRow12324.table (sourceIndex j)).centre) /
      (scalarRow12324.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12324.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12324Cell0
  | ⟨1,_⟩ => exact repair12324Cell1
  | ⟨2,_⟩ => exact repair12324Cell2
  | ⟨3,_⟩ => exact repair12324Cell3
  | ⟨4,_⟩ => exact repair12324Cell4
  | ⟨5,_⟩ => exact repair12324Cell5
  | ⟨6,_⟩ => exact repair12324Cell6
  | ⟨7,_⟩ => exact repair12324Cell7
  | ⟨8,_⟩ => exact repair12324Cell8
  | ⟨9,_⟩ => exact repair12324Cell9
  | ⟨10,_⟩ => exact repair12324Cell10
  | ⟨11,_⟩ => exact repair12324Cell11
  | ⟨12,_⟩ => exact repair12324Cell12
  | ⟨13,_⟩ => exact repair12324Cell13
  | ⟨14,_⟩ => exact repair12324Cell14
  | ⟨15,_⟩ => exact repair12324Cell15
  | ⟨16,_⟩ => exact repair12324Cell16
  | ⟨17,_⟩ => exact repair12324Cell17
  | ⟨18,_⟩ => exact repair12324Cell18
  | ⟨19,_⟩ => exact repair12324Cell19
  | ⟨20,_⟩ => exact repair12324Cell20
  | ⟨21,_⟩ => exact repair12324Cell21
  | ⟨22,_⟩ => exact repair12324Cell22
  | ⟨23,_⟩ => exact repair12324Cell23
  | ⟨24,_⟩ => exact repair12324Cell24
  | ⟨25,_⟩ => exact repair12324Cell25
  | ⟨26,_⟩ => exact repair12324Cell26
  | ⟨27,_⟩ => exact repair12324Cell27
  | ⟨28,_⟩ => exact repair12324Cell28
  | ⟨29,_⟩ => exact repair12324Cell29
  | ⟨30,_⟩ => exact repair12324Cell30
  | ⟨31,_⟩ => exact repair12324Cell31
  | ⟨32,_⟩ => exact repair12324Cell32
  | ⟨33,_⟩ => exact repair12324Cell33
  | ⟨34,_⟩ => exact repair12324Cell34
  | ⟨35,_⟩ => exact repair12324Cell35
  | ⟨36,_⟩ => exact repair12324Cell36
  | ⟨37,_⟩ => exact repair12324Cell37
  | ⟨38,_⟩ => exact repair12324Cell38
  | ⟨39,_⟩ => exact repair12324Cell39
  | ⟨40,_⟩ => exact repair12324Cell40
  | ⟨41,_⟩ => exact repair12324Cell41
  | ⟨42,_⟩ => exact repair12324Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12324 : FrameRepair 12324 scalarRow12324 where
  cap := cap12324
  cap_nonneg := fun j => (repair12324Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12324])
  endpoint := fun j => (repair12324Cells j).2.1
  endpoint_upper := fun j => (repair12324Cells j).2.2.1
  frame := fun j => (repair12324Cells j).2.2.2


end BstLean.Part264
