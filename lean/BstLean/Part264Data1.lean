import BstLean.Part264Repair
/-! Rational envelope and frame checks for each dimension. -/
namespace BstLean.Part264
open Real Set BstLean.Part255 BstLean.Part263
noncomputable def cap12250 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55190167 / 200000000 : ℝ)
  | ⟨1,_⟩ => (55270789 / 200000000 : ℝ)
  | ⟨2,_⟩ => (276756059 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (11086287 / 40000000 : ℝ)
  | ⟨4,_⟩ => (277557301 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (69489109 / 250000000 : ℝ)
  | ⟨6,_⟩ => (278354109 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (69687819 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279147467 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69885671 / 250000000 : ℝ)
  | ⟨10,_⟩ => (27993693 / 100000000 : ℝ)
  | ⟨11,_⟩ => (547519 / 1953125 : ℝ)
  | ⟨12,_⟩ => (280722047 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140556459 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140751861 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140946713 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141141093 / 500000000 : ℝ)
  | ⟨17,_⟩ => (141335007 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283056903 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283442863 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141913947 / 500000000 : ℝ)
  | ⟨21,_⟩ => (284212009 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (22234 / 78125 : ℝ)
  | ⟨23,_⟩ => (284976979 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (57071669 / 200000000 : ℝ)
  | ⟨25,_⟩ => (285738349 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (71529487 / 250000000 : ℝ)
  | ⟨27,_⟩ => (71624037 / 250000000 : ℝ)
  | ⟨28,_⟩ => (5737469 / 20000000 : ℝ)
  | ⟨29,_⟩ => (4488279 / 15625000 : ℝ)
  | ⟨30,_⟩ => (71906217 / 250000000 : ℝ)
  | ⟨31,_⟩ => (57599899 / 200000000 : ℝ)
  | ⟨32,_⟩ => (288373241 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72186399 / 250000000 : ℝ)
  | ⟨34,_⟩ => (11564683 / 40000000 : ℝ)
  | ⟨35,_⟩ => (289487683 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289857413 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290226283 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290594287 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145480459 / 500000000 : ℝ)
  | ⟨40,_⟩ => (29132669 / 100000000 : ℝ)
  | ⟨41,_⟩ => (29169161 / 100000000 : ℝ)
  | ⟨42,_⟩ => (146027839 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12250Cell0 :
    0 ≤ cap12250 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨0,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12250 ⟨0,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨0,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell1 :
    0 ≤ cap12250 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨1,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12250 ⟨1,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨1,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell2 :
    0 ≤ cap12250 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨2,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12250 ⟨2,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨2,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell3 :
    0 ≤ cap12250 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨3,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12250 ⟨3,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨3,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell4 :
    0 ≤ cap12250 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨4,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12250 ⟨4,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨4,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell5 :
    0 ≤ cap12250 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨5,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12250 ⟨5,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨5,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell6 :
    0 ≤ cap12250 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨6,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12250 ⟨6,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨6,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell7 :
    0 ≤ cap12250 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨7,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12250 ⟨7,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨7,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell8 :
    0 ≤ cap12250 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨8,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12250 ⟨8,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨8,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell9 :
    0 ≤ cap12250 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨9,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12250 ⟨9,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨9,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell10 :
    0 ≤ cap12250 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨10,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12250 ⟨10,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨10,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell11 :
    0 ≤ cap12250 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨11,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12250 ⟨11,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨11,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell12 :
    0 ≤ cap12250 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨12,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12250 ⟨12,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨12,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell13 :
    0 ≤ cap12250 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨13,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12250 ⟨13,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨13,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell14 :
    0 ≤ cap12250 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨14,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12250 ⟨14,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨14,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell15 :
    0 ≤ cap12250 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨15,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12250 ⟨15,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨15,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell16 :
    0 ≤ cap12250 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨16,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12250 ⟨16,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨16,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell17 :
    0 ≤ cap12250 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨17,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12250 ⟨17,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨17,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell18 :
    0 ≤ cap12250 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨18,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12250 ⟨18,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨18,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell19 :
    0 ≤ cap12250 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨19,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12250 ⟨19,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨19,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell20 :
    0 ≤ cap12250 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨20,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12250 ⟨20,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨20,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell21 :
    0 ≤ cap12250 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨21,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12250 ⟨21,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨21,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell22 :
    0 ≤ cap12250 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨22,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12250 ⟨22,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨22,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell23 :
    0 ≤ cap12250 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨23,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12250 ⟨23,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨23,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell24 :
    0 ≤ cap12250 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨24,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12250 ⟨24,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨24,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell25 :
    0 ≤ cap12250 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨25,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12250 ⟨25,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨25,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell26 :
    0 ≤ cap12250 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨26,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12250 ⟨26,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨26,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell27 :
    0 ≤ cap12250 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨27,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12250 ⟨27,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨27,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell28 :
    0 ≤ cap12250 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨28,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12250 ⟨28,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨28,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell29 :
    0 ≤ cap12250 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨29,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12250 ⟨29,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨29,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell30 :
    0 ≤ cap12250 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨30,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12250 ⟨30,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨30,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell31 :
    0 ≤ cap12250 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨31,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12250 ⟨31,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨31,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell32 :
    0 ≤ cap12250 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨32,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12250 ⟨32,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨32,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell33 :
    0 ≤ cap12250 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨33,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12250 ⟨33,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨33,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell34 :
    0 ≤ cap12250 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨34,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12250 ⟨34,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨34,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell35 :
    0 ≤ cap12250 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨35,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12250 ⟨35,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨35,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell36 :
    0 ≤ cap12250 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨36,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12250 ⟨36,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨36,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell37 :
    0 ≤ cap12250 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨37,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12250 ⟨37,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨37,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell38 :
    0 ≤ cap12250 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨38,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12250 ⟨38,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨38,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell39 :
    0 ≤ cap12250 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨39,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12250 ⟨39,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨39,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell40 :
    0 ≤ cap12250 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨40,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12250 ⟨40,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨40,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell41 :
    0 ≤ cap12250 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨41,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12250 ⟨41,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨41,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cell42 :
    0 ≤ cap12250 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12250 (parameters ⟨42,by decide⟩)
      (scalarRow12250.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12250 ⟨42,by decide⟩ ∧
    (scalarRow12250.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 ⟨42,by decide⟩ + (scalarRow12250.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12250.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12250.targetFrame := by
  norm_num [cap12250, scalarRow12250, sourceIndex, cell12250, BstLean.Part263.envelope, parameters]

theorem repair12250Cells (j : Fin 43) :
    0 ≤ cap12250 j ∧
    BstLean.Part263.envelope 12250 (parameters j) (scalarRow12250.table (sourceIndex j)).upper ≤ cap12250 j ∧
    (scalarRow12250.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12250 j + (scalarRow12250.table (sourceIndex j)).centre) /
      (scalarRow12250.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12250.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12250Cell0
  | ⟨1,_⟩ => exact repair12250Cell1
  | ⟨2,_⟩ => exact repair12250Cell2
  | ⟨3,_⟩ => exact repair12250Cell3
  | ⟨4,_⟩ => exact repair12250Cell4
  | ⟨5,_⟩ => exact repair12250Cell5
  | ⟨6,_⟩ => exact repair12250Cell6
  | ⟨7,_⟩ => exact repair12250Cell7
  | ⟨8,_⟩ => exact repair12250Cell8
  | ⟨9,_⟩ => exact repair12250Cell9
  | ⟨10,_⟩ => exact repair12250Cell10
  | ⟨11,_⟩ => exact repair12250Cell11
  | ⟨12,_⟩ => exact repair12250Cell12
  | ⟨13,_⟩ => exact repair12250Cell13
  | ⟨14,_⟩ => exact repair12250Cell14
  | ⟨15,_⟩ => exact repair12250Cell15
  | ⟨16,_⟩ => exact repair12250Cell16
  | ⟨17,_⟩ => exact repair12250Cell17
  | ⟨18,_⟩ => exact repair12250Cell18
  | ⟨19,_⟩ => exact repair12250Cell19
  | ⟨20,_⟩ => exact repair12250Cell20
  | ⟨21,_⟩ => exact repair12250Cell21
  | ⟨22,_⟩ => exact repair12250Cell22
  | ⟨23,_⟩ => exact repair12250Cell23
  | ⟨24,_⟩ => exact repair12250Cell24
  | ⟨25,_⟩ => exact repair12250Cell25
  | ⟨26,_⟩ => exact repair12250Cell26
  | ⟨27,_⟩ => exact repair12250Cell27
  | ⟨28,_⟩ => exact repair12250Cell28
  | ⟨29,_⟩ => exact repair12250Cell29
  | ⟨30,_⟩ => exact repair12250Cell30
  | ⟨31,_⟩ => exact repair12250Cell31
  | ⟨32,_⟩ => exact repair12250Cell32
  | ⟨33,_⟩ => exact repair12250Cell33
  | ⟨34,_⟩ => exact repair12250Cell34
  | ⟨35,_⟩ => exact repair12250Cell35
  | ⟨36,_⟩ => exact repair12250Cell36
  | ⟨37,_⟩ => exact repair12250Cell37
  | ⟨38,_⟩ => exact repair12250Cell38
  | ⟨39,_⟩ => exact repair12250Cell39
  | ⟨40,_⟩ => exact repair12250Cell40
  | ⟨41,_⟩ => exact repair12250Cell41
  | ⟨42,_⟩ => exact repair12250Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12250 : FrameRepair 12250 scalarRow12250 where
  cap := cap12250
  cap_nonneg := fun j => (repair12250Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12250])
  endpoint := fun j => (repair12250Cells j).2.1
  endpoint_upper := fun j => (repair12250Cells j).2.2.1
  frame := fun j => (repair12250Cells j).2.2.2

noncomputable def cap12251 : Fin 43 → ℝ
  | ⟨0,_⟩ => (6898769 / 25000000 : ℝ)
  | ⟨1,_⟩ => (138176931 / 500000000 : ℝ)
  | ⟨2,_⟩ => (27675597 / 100000000 : ℝ)
  | ⟨3,_⟩ => (6928927 / 25000000 : ℝ)
  | ⟨4,_⟩ => (277557199 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277956327 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55670799 / 200000000 : ℝ)
  | ⟨7,_⟩ => (55750231 / 200000000 : ℝ)
  | ⟨8,_⟩ => (279147339 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (5590851 / 20000000 : ℝ)
  | ⟨10,_⟩ => (27993679 / 100000000 : ℝ)
  | ⟨11,_⟩ => (280329581 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (140360947 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281112759 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (70375889 / 250000000 : ℝ)
  | ⟨15,_⟩ => (140946627 / 500000000 : ℝ)
  | ⟨16,_⟩ => (35285251 / 125000000 : ℝ)
  | ⟨17,_⟩ => (28266983 / 100000000 : ℝ)
  | ⟨18,_⟩ => (35382089 / 125000000 : ℝ)
  | ⟨19,_⟩ => (56688533 / 200000000 : ℝ)
  | ⟨20,_⟩ => (283827691 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (1421059 / 5000000 : ℝ)
  | ⟨22,_⟩ => (35574373 / 125000000 : ℝ)
  | ⟨23,_⟩ => (284976757 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285358117 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (57147623 / 200000000 : ℝ)
  | ⟨26,_⟩ => (71529427 / 250000000 : ℝ)
  | ⟨27,_⟩ => (286495901 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286873197 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287249597 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287624603 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (35999903 / 125000000 : ℝ)
  | ⟨32,_⟩ => (72093241 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288745313 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144558393 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289487387 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289857111 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (11609039 / 40000000 : ℝ)
  | ⟨38,_⟩ => (290593973 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290960599 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58265273 / 200000000 : ℝ)
  | ⟨41,_⟩ => (291691279 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (14602767 / 50000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12251Cell0 :
    0 ≤ cap12251 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨0,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12251 ⟨0,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨0,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell1 :
    0 ≤ cap12251 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨1,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12251 ⟨1,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨1,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell2 :
    0 ≤ cap12251 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨2,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12251 ⟨2,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨2,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell3 :
    0 ≤ cap12251 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨3,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12251 ⟨3,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨3,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell4 :
    0 ≤ cap12251 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨4,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12251 ⟨4,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨4,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell5 :
    0 ≤ cap12251 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨5,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12251 ⟨5,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨5,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell6 :
    0 ≤ cap12251 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨6,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12251 ⟨6,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨6,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell7 :
    0 ≤ cap12251 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨7,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12251 ⟨7,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨7,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell8 :
    0 ≤ cap12251 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨8,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12251 ⟨8,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨8,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell9 :
    0 ≤ cap12251 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨9,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12251 ⟨9,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨9,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell10 :
    0 ≤ cap12251 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨10,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12251 ⟨10,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨10,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell11 :
    0 ≤ cap12251 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨11,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12251 ⟨11,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨11,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell12 :
    0 ≤ cap12251 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨12,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12251 ⟨12,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨12,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell13 :
    0 ≤ cap12251 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨13,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12251 ⟨13,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨13,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell14 :
    0 ≤ cap12251 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨14,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12251 ⟨14,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨14,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell15 :
    0 ≤ cap12251 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨15,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12251 ⟨15,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨15,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell16 :
    0 ≤ cap12251 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨16,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12251 ⟨16,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨16,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell17 :
    0 ≤ cap12251 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨17,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12251 ⟨17,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨17,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell18 :
    0 ≤ cap12251 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨18,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12251 ⟨18,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨18,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell19 :
    0 ≤ cap12251 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨19,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12251 ⟨19,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨19,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell20 :
    0 ≤ cap12251 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨20,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12251 ⟨20,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨20,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell21 :
    0 ≤ cap12251 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨21,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12251 ⟨21,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨21,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell22 :
    0 ≤ cap12251 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨22,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12251 ⟨22,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨22,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell23 :
    0 ≤ cap12251 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨23,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12251 ⟨23,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨23,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell24 :
    0 ≤ cap12251 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨24,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12251 ⟨24,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨24,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell25 :
    0 ≤ cap12251 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨25,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12251 ⟨25,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨25,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell26 :
    0 ≤ cap12251 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨26,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12251 ⟨26,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨26,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell27 :
    0 ≤ cap12251 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨27,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12251 ⟨27,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨27,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell28 :
    0 ≤ cap12251 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨28,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12251 ⟨28,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨28,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell29 :
    0 ≤ cap12251 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨29,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12251 ⟨29,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨29,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell30 :
    0 ≤ cap12251 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨30,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12251 ⟨30,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨30,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell31 :
    0 ≤ cap12251 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨31,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12251 ⟨31,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨31,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell32 :
    0 ≤ cap12251 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨32,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12251 ⟨32,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨32,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell33 :
    0 ≤ cap12251 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨33,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12251 ⟨33,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨33,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell34 :
    0 ≤ cap12251 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨34,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12251 ⟨34,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨34,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell35 :
    0 ≤ cap12251 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨35,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12251 ⟨35,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨35,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell36 :
    0 ≤ cap12251 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨36,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12251 ⟨36,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨36,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell37 :
    0 ≤ cap12251 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨37,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12251 ⟨37,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨37,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell38 :
    0 ≤ cap12251 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨38,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12251 ⟨38,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨38,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell39 :
    0 ≤ cap12251 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨39,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12251 ⟨39,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨39,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell40 :
    0 ≤ cap12251 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨40,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12251 ⟨40,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨40,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell41 :
    0 ≤ cap12251 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨41,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12251 ⟨41,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨41,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cell42 :
    0 ≤ cap12251 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12251 (parameters ⟨42,by decide⟩)
      (scalarRow12251.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12251 ⟨42,by decide⟩ ∧
    (scalarRow12251.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 ⟨42,by decide⟩ + (scalarRow12251.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12251.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12251.targetFrame := by
  norm_num [cap12251, scalarRow12251, sourceIndex, cell12251, BstLean.Part263.envelope, parameters]

theorem repair12251Cells (j : Fin 43) :
    0 ≤ cap12251 j ∧
    BstLean.Part263.envelope 12251 (parameters j) (scalarRow12251.table (sourceIndex j)).upper ≤ cap12251 j ∧
    (scalarRow12251.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12251 j + (scalarRow12251.table (sourceIndex j)).centre) /
      (scalarRow12251.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12251.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12251Cell0
  | ⟨1,_⟩ => exact repair12251Cell1
  | ⟨2,_⟩ => exact repair12251Cell2
  | ⟨3,_⟩ => exact repair12251Cell3
  | ⟨4,_⟩ => exact repair12251Cell4
  | ⟨5,_⟩ => exact repair12251Cell5
  | ⟨6,_⟩ => exact repair12251Cell6
  | ⟨7,_⟩ => exact repair12251Cell7
  | ⟨8,_⟩ => exact repair12251Cell8
  | ⟨9,_⟩ => exact repair12251Cell9
  | ⟨10,_⟩ => exact repair12251Cell10
  | ⟨11,_⟩ => exact repair12251Cell11
  | ⟨12,_⟩ => exact repair12251Cell12
  | ⟨13,_⟩ => exact repair12251Cell13
  | ⟨14,_⟩ => exact repair12251Cell14
  | ⟨15,_⟩ => exact repair12251Cell15
  | ⟨16,_⟩ => exact repair12251Cell16
  | ⟨17,_⟩ => exact repair12251Cell17
  | ⟨18,_⟩ => exact repair12251Cell18
  | ⟨19,_⟩ => exact repair12251Cell19
  | ⟨20,_⟩ => exact repair12251Cell20
  | ⟨21,_⟩ => exact repair12251Cell21
  | ⟨22,_⟩ => exact repair12251Cell22
  | ⟨23,_⟩ => exact repair12251Cell23
  | ⟨24,_⟩ => exact repair12251Cell24
  | ⟨25,_⟩ => exact repair12251Cell25
  | ⟨26,_⟩ => exact repair12251Cell26
  | ⟨27,_⟩ => exact repair12251Cell27
  | ⟨28,_⟩ => exact repair12251Cell28
  | ⟨29,_⟩ => exact repair12251Cell29
  | ⟨30,_⟩ => exact repair12251Cell30
  | ⟨31,_⟩ => exact repair12251Cell31
  | ⟨32,_⟩ => exact repair12251Cell32
  | ⟨33,_⟩ => exact repair12251Cell33
  | ⟨34,_⟩ => exact repair12251Cell34
  | ⟨35,_⟩ => exact repair12251Cell35
  | ⟨36,_⟩ => exact repair12251Cell36
  | ⟨37,_⟩ => exact repair12251Cell37
  | ⟨38,_⟩ => exact repair12251Cell38
  | ⟨39,_⟩ => exact repair12251Cell39
  | ⟨40,_⟩ => exact repair12251Cell40
  | ⟨41,_⟩ => exact repair12251Cell41
  | ⟨42,_⟩ => exact repair12251Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12251 : FrameRepair 12251 scalarRow12251 where
  cap := cap12251
  cap_nonneg := fun j => (repair12251Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12251])
  endpoint := fun j => (repair12251Cells j).2.1
  endpoint_upper := fun j => (repair12251Cells j).2.2.1
  frame := fun j => (repair12251Cells j).2.2.2

noncomputable def cap12252 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68987671 / 250000000 : ℝ)
  | ⟨1,_⟩ => (13817689 / 50000000 : ℝ)
  | ⟨2,_⟩ => (138377941 / 500000000 : ℝ)
  | ⟨3,_⟩ => (55431397 / 200000000 : ℝ)
  | ⟨4,_⟩ => (277557097 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277956219 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (6958847 / 25000000 : ℝ)
  | ⟨7,_⟩ => (139375517 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69786803 / 250000000 : ℝ)
  | ⟨9,_⟩ => (17471401 / 62500000 : ℝ)
  | ⟨10,_⟩ => (5598733 / 20000000 : ℝ)
  | ⟨11,_⟩ => (140164717 / 500000000 : ℝ)
  | ⟨12,_⟩ => (280721741 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (1405563 / 5000000 : ℝ)
  | ⟨14,_⟩ => (281503391 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140946541 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282281829 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (56533929 / 200000000 : ℝ)
  | ⟨18,_⟩ => (283056521 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (70860617 / 250000000 : ℝ)
  | ⟨20,_⟩ => (8869609 / 31250000 : ℝ)
  | ⟨21,_⟩ => (28421159 / 100000000 : ℝ)
  | ⟨22,_⟩ => (17787173 / 62500000 : ℝ)
  | ⟨23,_⟩ => (56995307 / 200000000 : ℝ)
  | ⟨24,_⟩ => (4458717 / 15625000 : ℝ)
  | ⟨25,_⟩ => (7143447 / 25000000 : ℝ)
  | ⟨26,_⟩ => (286117467 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143247827 / 500000000 : ℝ)
  | ⟨28,_⟩ => (17929559 / 62500000 : ℝ)
  | ⟨29,_⟩ => (143624669 / 500000000 : ℝ)
  | ⟨30,_⟩ => (143812169 / 500000000 : ℝ)
  | ⟨31,_⟩ => (287998953 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288372687 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288745029 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289116497 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72371773 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289856809 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290225667 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (14529683 / 50000000 : ℝ)
  | ⟨39,_⟩ => (290960279 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291326039 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291690947 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292055003 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12252Cell0 :
    0 ≤ cap12252 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨0,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12252 ⟨0,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨0,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell1 :
    0 ≤ cap12252 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨1,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12252 ⟨1,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨1,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell2 :
    0 ≤ cap12252 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨2,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12252 ⟨2,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨2,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell3 :
    0 ≤ cap12252 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨3,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12252 ⟨3,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨3,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell4 :
    0 ≤ cap12252 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨4,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12252 ⟨4,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨4,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell5 :
    0 ≤ cap12252 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨5,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12252 ⟨5,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨5,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell6 :
    0 ≤ cap12252 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨6,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12252 ⟨6,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨6,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell7 :
    0 ≤ cap12252 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨7,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12252 ⟨7,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨7,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell8 :
    0 ≤ cap12252 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨8,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12252 ⟨8,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨8,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell9 :
    0 ≤ cap12252 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨9,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12252 ⟨9,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨9,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell10 :
    0 ≤ cap12252 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨10,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12252 ⟨10,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨10,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell11 :
    0 ≤ cap12252 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨11,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12252 ⟨11,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨11,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell12 :
    0 ≤ cap12252 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨12,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12252 ⟨12,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨12,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell13 :
    0 ≤ cap12252 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨13,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12252 ⟨13,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨13,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell14 :
    0 ≤ cap12252 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨14,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12252 ⟨14,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨14,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell15 :
    0 ≤ cap12252 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨15,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12252 ⟨15,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨15,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell16 :
    0 ≤ cap12252 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨16,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12252 ⟨16,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨16,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell17 :
    0 ≤ cap12252 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨17,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12252 ⟨17,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨17,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell18 :
    0 ≤ cap12252 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨18,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12252 ⟨18,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨18,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell19 :
    0 ≤ cap12252 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨19,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12252 ⟨19,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨19,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell20 :
    0 ≤ cap12252 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨20,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12252 ⟨20,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨20,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell21 :
    0 ≤ cap12252 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨21,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12252 ⟨21,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨21,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell22 :
    0 ≤ cap12252 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨22,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12252 ⟨22,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨22,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell23 :
    0 ≤ cap12252 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨23,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12252 ⟨23,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨23,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell24 :
    0 ≤ cap12252 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨24,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12252 ⟨24,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨24,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell25 :
    0 ≤ cap12252 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨25,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12252 ⟨25,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨25,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell26 :
    0 ≤ cap12252 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨26,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12252 ⟨26,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨26,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell27 :
    0 ≤ cap12252 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨27,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12252 ⟨27,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨27,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell28 :
    0 ≤ cap12252 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨28,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12252 ⟨28,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨28,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell29 :
    0 ≤ cap12252 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨29,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12252 ⟨29,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨29,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell30 :
    0 ≤ cap12252 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨30,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12252 ⟨30,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨30,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell31 :
    0 ≤ cap12252 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨31,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12252 ⟨31,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨31,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell32 :
    0 ≤ cap12252 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨32,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12252 ⟨32,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨32,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell33 :
    0 ≤ cap12252 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨33,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12252 ⟨33,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨33,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell34 :
    0 ≤ cap12252 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨34,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12252 ⟨34,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨34,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell35 :
    0 ≤ cap12252 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨35,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12252 ⟨35,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨35,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell36 :
    0 ≤ cap12252 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨36,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12252 ⟨36,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨36,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell37 :
    0 ≤ cap12252 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨37,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12252 ⟨37,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨37,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell38 :
    0 ≤ cap12252 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨38,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12252 ⟨38,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨38,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell39 :
    0 ≤ cap12252 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨39,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12252 ⟨39,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨39,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell40 :
    0 ≤ cap12252 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨40,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12252 ⟨40,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨40,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell41 :
    0 ≤ cap12252 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨41,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12252 ⟨41,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨41,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cell42 :
    0 ≤ cap12252 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12252 (parameters ⟨42,by decide⟩)
      (scalarRow12252.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12252 ⟨42,by decide⟩ ∧
    (scalarRow12252.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 ⟨42,by decide⟩ + (scalarRow12252.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12252.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12252.targetFrame := by
  norm_num [cap12252, scalarRow12252, sourceIndex, cell12252, BstLean.Part263.envelope, parameters]

theorem repair12252Cells (j : Fin 43) :
    0 ≤ cap12252 j ∧
    BstLean.Part263.envelope 12252 (parameters j) (scalarRow12252.table (sourceIndex j)).upper ≤ cap12252 j ∧
    (scalarRow12252.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12252 j + (scalarRow12252.table (sourceIndex j)).centre) /
      (scalarRow12252.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12252.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12252Cell0
  | ⟨1,_⟩ => exact repair12252Cell1
  | ⟨2,_⟩ => exact repair12252Cell2
  | ⟨3,_⟩ => exact repair12252Cell3
  | ⟨4,_⟩ => exact repair12252Cell4
  | ⟨5,_⟩ => exact repair12252Cell5
  | ⟨6,_⟩ => exact repair12252Cell6
  | ⟨7,_⟩ => exact repair12252Cell7
  | ⟨8,_⟩ => exact repair12252Cell8
  | ⟨9,_⟩ => exact repair12252Cell9
  | ⟨10,_⟩ => exact repair12252Cell10
  | ⟨11,_⟩ => exact repair12252Cell11
  | ⟨12,_⟩ => exact repair12252Cell12
  | ⟨13,_⟩ => exact repair12252Cell13
  | ⟨14,_⟩ => exact repair12252Cell14
  | ⟨15,_⟩ => exact repair12252Cell15
  | ⟨16,_⟩ => exact repair12252Cell16
  | ⟨17,_⟩ => exact repair12252Cell17
  | ⟨18,_⟩ => exact repair12252Cell18
  | ⟨19,_⟩ => exact repair12252Cell19
  | ⟨20,_⟩ => exact repair12252Cell20
  | ⟨21,_⟩ => exact repair12252Cell21
  | ⟨22,_⟩ => exact repair12252Cell22
  | ⟨23,_⟩ => exact repair12252Cell23
  | ⟨24,_⟩ => exact repair12252Cell24
  | ⟨25,_⟩ => exact repair12252Cell25
  | ⟨26,_⟩ => exact repair12252Cell26
  | ⟨27,_⟩ => exact repair12252Cell27
  | ⟨28,_⟩ => exact repair12252Cell28
  | ⟨29,_⟩ => exact repair12252Cell29
  | ⟨30,_⟩ => exact repair12252Cell30
  | ⟨31,_⟩ => exact repair12252Cell31
  | ⟨32,_⟩ => exact repair12252Cell32
  | ⟨33,_⟩ => exact repair12252Cell33
  | ⟨34,_⟩ => exact repair12252Cell34
  | ⟨35,_⟩ => exact repair12252Cell35
  | ⟨36,_⟩ => exact repair12252Cell36
  | ⟨37,_⟩ => exact repair12252Cell37
  | ⟨38,_⟩ => exact repair12252Cell38
  | ⟨39,_⟩ => exact repair12252Cell39
  | ⟨40,_⟩ => exact repair12252Cell40
  | ⟨41,_⟩ => exact repair12252Cell41
  | ⟨42,_⟩ => exact repair12252Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12252 : FrameRepair 12252 scalarRow12252 where
  cap := cap12252
  cap_nonneg := fun j => (repair12252Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12252])
  endpoint := fun j => (repair12252Cells j).2.1
  endpoint_upper := fun j => (repair12252Cells j).2.2.1
  frame := fun j => (repair12252Cells j).2.2.2

noncomputable def cap12253 : Fin 43 → ℝ
  | ⟨0,_⟩ => (17246913 / 62500000 : ℝ)
  | ⟨1,_⟩ => (138176849 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276755793 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (27715689 / 100000000 : ℝ)
  | ⟨4,_⟩ => (55511399 / 200000000 : ℝ)
  | ⟨5,_⟩ => (277956111 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55670753 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278750913 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (69786771 / 250000000 : ℝ)
  | ⟨9,_⟩ => (279542283 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (27993651 / 100000000 : ℝ)
  | ⟨11,_⟩ => (35041161 / 125000000 : ℝ)
  | ⟨12,_⟩ => (70180397 / 250000000 : ℝ)
  | ⟨13,_⟩ => (7027811 / 25000000 : ℝ)
  | ⟨14,_⟩ => (11260129 / 40000000 : ℝ)
  | ⟨15,_⟩ => (28189291 / 100000000 : ℝ)
  | ⟨16,_⟩ => (282281651 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282669461 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (28305633 / 100000000 : ℝ)
  | ⟨19,_⟩ => (283442271 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (70956821 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284211381 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (35574319 / 125000000 : ℝ)
  | ⟨23,_⟩ => (284976313 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (14267883 / 50000000 : ℝ)
  | ⟨25,_⟩ => (142868823 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286117227 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (17905963 / 62500000 : ℝ)
  | ⟨28,_⟩ => (71718173 / 250000000 : ℝ)
  | ⟨29,_⟩ => (287249079 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287624073 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143999341 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288372409 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144372373 / 500000000 : ℝ)
  | ⟨34,_⟩ => (289116207 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (72371699 / 250000000 : ℝ)
  | ⟨36,_⟩ => (72464127 / 250000000 : ℝ)
  | ⟨37,_⟩ => (3627817 / 12500000 : ℝ)
  | ⟨38,_⟩ => (145296673 / 500000000 : ℝ)
  | ⟨39,_⟩ => (7273999 / 25000000 : ℝ)
  | ⟨40,_⟩ => (145662857 / 500000000 : ℝ)
  | ⟨41,_⟩ => (36461327 / 125000000 : ℝ)
  | ⟨42,_⟩ => (58410933 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12253Cell0 :
    0 ≤ cap12253 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨0,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12253 ⟨0,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨0,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell1 :
    0 ≤ cap12253 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨1,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12253 ⟨1,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨1,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell2 :
    0 ≤ cap12253 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨2,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12253 ⟨2,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨2,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell3 :
    0 ≤ cap12253 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨3,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12253 ⟨3,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨3,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell4 :
    0 ≤ cap12253 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨4,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12253 ⟨4,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨4,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell5 :
    0 ≤ cap12253 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨5,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12253 ⟨5,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨5,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell6 :
    0 ≤ cap12253 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨6,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12253 ⟨6,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨6,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell7 :
    0 ≤ cap12253 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨7,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12253 ⟨7,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨7,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell8 :
    0 ≤ cap12253 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨8,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12253 ⟨8,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨8,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell9 :
    0 ≤ cap12253 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨9,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12253 ⟨9,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨9,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell10 :
    0 ≤ cap12253 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨10,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12253 ⟨10,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨10,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell11 :
    0 ≤ cap12253 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨11,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12253 ⟨11,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨11,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell12 :
    0 ≤ cap12253 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨12,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12253 ⟨12,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨12,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell13 :
    0 ≤ cap12253 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨13,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12253 ⟨13,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨13,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell14 :
    0 ≤ cap12253 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨14,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12253 ⟨14,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨14,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell15 :
    0 ≤ cap12253 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨15,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12253 ⟨15,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨15,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell16 :
    0 ≤ cap12253 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨16,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12253 ⟨16,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨16,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell17 :
    0 ≤ cap12253 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨17,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12253 ⟨17,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨17,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell18 :
    0 ≤ cap12253 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨18,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12253 ⟨18,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨18,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell19 :
    0 ≤ cap12253 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨19,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12253 ⟨19,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨19,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell20 :
    0 ≤ cap12253 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨20,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12253 ⟨20,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨20,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell21 :
    0 ≤ cap12253 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨21,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12253 ⟨21,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨21,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell22 :
    0 ≤ cap12253 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨22,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12253 ⟨22,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨22,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell23 :
    0 ≤ cap12253 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨23,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12253 ⟨23,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨23,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell24 :
    0 ≤ cap12253 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨24,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12253 ⟨24,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨24,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell25 :
    0 ≤ cap12253 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨25,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12253 ⟨25,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨25,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell26 :
    0 ≤ cap12253 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨26,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12253 ⟨26,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨26,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell27 :
    0 ≤ cap12253 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨27,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12253 ⟨27,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨27,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell28 :
    0 ≤ cap12253 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨28,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12253 ⟨28,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨28,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell29 :
    0 ≤ cap12253 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨29,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12253 ⟨29,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨29,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell30 :
    0 ≤ cap12253 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨30,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12253 ⟨30,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨30,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell31 :
    0 ≤ cap12253 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨31,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12253 ⟨31,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨31,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell32 :
    0 ≤ cap12253 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨32,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12253 ⟨32,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨32,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell33 :
    0 ≤ cap12253 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨33,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12253 ⟨33,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨33,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell34 :
    0 ≤ cap12253 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨34,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12253 ⟨34,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨34,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell35 :
    0 ≤ cap12253 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨35,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12253 ⟨35,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨35,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell36 :
    0 ≤ cap12253 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨36,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12253 ⟨36,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨36,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell37 :
    0 ≤ cap12253 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨37,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12253 ⟨37,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨37,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell38 :
    0 ≤ cap12253 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨38,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12253 ⟨38,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨38,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell39 :
    0 ≤ cap12253 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨39,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12253 ⟨39,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨39,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell40 :
    0 ≤ cap12253 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨40,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12253 ⟨40,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨40,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell41 :
    0 ≤ cap12253 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨41,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12253 ⟨41,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨41,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cell42 :
    0 ≤ cap12253 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12253 (parameters ⟨42,by decide⟩)
      (scalarRow12253.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12253 ⟨42,by decide⟩ ∧
    (scalarRow12253.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 ⟨42,by decide⟩ + (scalarRow12253.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12253.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12253.targetFrame := by
  norm_num [cap12253, scalarRow12253, sourceIndex, cell12253, BstLean.Part263.envelope, parameters]

theorem repair12253Cells (j : Fin 43) :
    0 ≤ cap12253 j ∧
    BstLean.Part263.envelope 12253 (parameters j) (scalarRow12253.table (sourceIndex j)).upper ≤ cap12253 j ∧
    (scalarRow12253.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12253 j + (scalarRow12253.table (sourceIndex j)).centre) /
      (scalarRow12253.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12253.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12253Cell0
  | ⟨1,_⟩ => exact repair12253Cell1
  | ⟨2,_⟩ => exact repair12253Cell2
  | ⟨3,_⟩ => exact repair12253Cell3
  | ⟨4,_⟩ => exact repair12253Cell4
  | ⟨5,_⟩ => exact repair12253Cell5
  | ⟨6,_⟩ => exact repair12253Cell6
  | ⟨7,_⟩ => exact repair12253Cell7
  | ⟨8,_⟩ => exact repair12253Cell8
  | ⟨9,_⟩ => exact repair12253Cell9
  | ⟨10,_⟩ => exact repair12253Cell10
  | ⟨11,_⟩ => exact repair12253Cell11
  | ⟨12,_⟩ => exact repair12253Cell12
  | ⟨13,_⟩ => exact repair12253Cell13
  | ⟨14,_⟩ => exact repair12253Cell14
  | ⟨15,_⟩ => exact repair12253Cell15
  | ⟨16,_⟩ => exact repair12253Cell16
  | ⟨17,_⟩ => exact repair12253Cell17
  | ⟨18,_⟩ => exact repair12253Cell18
  | ⟨19,_⟩ => exact repair12253Cell19
  | ⟨20,_⟩ => exact repair12253Cell20
  | ⟨21,_⟩ => exact repair12253Cell21
  | ⟨22,_⟩ => exact repair12253Cell22
  | ⟨23,_⟩ => exact repair12253Cell23
  | ⟨24,_⟩ => exact repair12253Cell24
  | ⟨25,_⟩ => exact repair12253Cell25
  | ⟨26,_⟩ => exact repair12253Cell26
  | ⟨27,_⟩ => exact repair12253Cell27
  | ⟨28,_⟩ => exact repair12253Cell28
  | ⟨29,_⟩ => exact repair12253Cell29
  | ⟨30,_⟩ => exact repair12253Cell30
  | ⟨31,_⟩ => exact repair12253Cell31
  | ⟨32,_⟩ => exact repair12253Cell32
  | ⟨33,_⟩ => exact repair12253Cell33
  | ⟨34,_⟩ => exact repair12253Cell34
  | ⟨35,_⟩ => exact repair12253Cell35
  | ⟨36,_⟩ => exact repair12253Cell36
  | ⟨37,_⟩ => exact repair12253Cell37
  | ⟨38,_⟩ => exact repair12253Cell38
  | ⟨39,_⟩ => exact repair12253Cell39
  | ⟨40,_⟩ => exact repair12253Cell40
  | ⟨41,_⟩ => exact repair12253Cell41
  | ⟨42,_⟩ => exact repair12253Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12253 : FrameRepair 12253 scalarRow12253 where
  cap := cap12253
  cap_nonneg := fun j => (repair12253Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12253])
  endpoint := fun j => (repair12253Cells j).2.1
  endpoint_upper := fun j => (repair12253Cells j).2.2.1
  frame := fun j => (repair12253Cells j).2.2.2

noncomputable def cap12254 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68987633 / 250000000 : ℝ)
  | ⟨1,_⟩ => (17272101 / 62500000 : ℝ)
  | ⟨2,_⟩ => (34594463 / 125000000 : ℝ)
  | ⟨3,_⟩ => (138578397 / 500000000 : ℝ)
  | ⟨4,_⟩ => (138778447 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277956003 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278353651 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (34843849 / 125000000 : ℝ)
  | ⟨8,_⟩ => (279146957 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279542149 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279936369 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280329141 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (56144287 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281112281 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (14075153 / 50000000 : ℝ)
  | ⟨15,_⟩ => (140946369 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282281473 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (70667319 / 250000000 : ℝ)
  | ⟨18,_⟩ => (14152807 / 50000000 : ℝ)
  | ⟨19,_⟩ => (141721037 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283827081 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284211171 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284594337 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284976091 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (35669679 / 125000000 : ℝ)
  | ⟨25,_⟩ => (71434353 / 250000000 : ℝ)
  | ⟨26,_⟩ => (143058493 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286495161 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286872439 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (14362441 / 50000000 : ℝ)
  | ⟨30,_⟩ => (2247061 / 7812500 : ℝ)
  | ⟨31,_⟩ => (287998411 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (72093033 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288744463 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144557959 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289486501 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144928103 / 500000000 : ℝ)
  | ⟨37,_⟩ => (72556263 / 250000000 : ℝ)
  | ⟨38,_⟩ => (290593033 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (7273991 / 25000000 : ℝ)
  | ⟨40,_⟩ => (72831347 / 250000000 : ℝ)
  | ⟨41,_⟩ => (72922571 / 250000000 : ℝ)
  | ⟨42,_⟩ => (36506791 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12254Cell0 :
    0 ≤ cap12254 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨0,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12254 ⟨0,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨0,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell1 :
    0 ≤ cap12254 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨1,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12254 ⟨1,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨1,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell2 :
    0 ≤ cap12254 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨2,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12254 ⟨2,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨2,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell3 :
    0 ≤ cap12254 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨3,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12254 ⟨3,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨3,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell4 :
    0 ≤ cap12254 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨4,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12254 ⟨4,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨4,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell5 :
    0 ≤ cap12254 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨5,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12254 ⟨5,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨5,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell6 :
    0 ≤ cap12254 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨6,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12254 ⟨6,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨6,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell7 :
    0 ≤ cap12254 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨7,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12254 ⟨7,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨7,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell8 :
    0 ≤ cap12254 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨8,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12254 ⟨8,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨8,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell9 :
    0 ≤ cap12254 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨9,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12254 ⟨9,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨9,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell10 :
    0 ≤ cap12254 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨10,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12254 ⟨10,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨10,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell11 :
    0 ≤ cap12254 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨11,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12254 ⟨11,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨11,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell12 :
    0 ≤ cap12254 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨12,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12254 ⟨12,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨12,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell13 :
    0 ≤ cap12254 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨13,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12254 ⟨13,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨13,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell14 :
    0 ≤ cap12254 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨14,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12254 ⟨14,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨14,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell15 :
    0 ≤ cap12254 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨15,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12254 ⟨15,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨15,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell16 :
    0 ≤ cap12254 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨16,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12254 ⟨16,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨16,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell17 :
    0 ≤ cap12254 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨17,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12254 ⟨17,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨17,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell18 :
    0 ≤ cap12254 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨18,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12254 ⟨18,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨18,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell19 :
    0 ≤ cap12254 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨19,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12254 ⟨19,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨19,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell20 :
    0 ≤ cap12254 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨20,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12254 ⟨20,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨20,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell21 :
    0 ≤ cap12254 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨21,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12254 ⟨21,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨21,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell22 :
    0 ≤ cap12254 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨22,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12254 ⟨22,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨22,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell23 :
    0 ≤ cap12254 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨23,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12254 ⟨23,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨23,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell24 :
    0 ≤ cap12254 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨24,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12254 ⟨24,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨24,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell25 :
    0 ≤ cap12254 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨25,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12254 ⟨25,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨25,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell26 :
    0 ≤ cap12254 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨26,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12254 ⟨26,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨26,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell27 :
    0 ≤ cap12254 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨27,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12254 ⟨27,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨27,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell28 :
    0 ≤ cap12254 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨28,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12254 ⟨28,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨28,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell29 :
    0 ≤ cap12254 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨29,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12254 ⟨29,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨29,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell30 :
    0 ≤ cap12254 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨30,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12254 ⟨30,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨30,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell31 :
    0 ≤ cap12254 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨31,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12254 ⟨31,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨31,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell32 :
    0 ≤ cap12254 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨32,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12254 ⟨32,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨32,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell33 :
    0 ≤ cap12254 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨33,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12254 ⟨33,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨33,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell34 :
    0 ≤ cap12254 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨34,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12254 ⟨34,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨34,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell35 :
    0 ≤ cap12254 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨35,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12254 ⟨35,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨35,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell36 :
    0 ≤ cap12254 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨36,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12254 ⟨36,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨36,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell37 :
    0 ≤ cap12254 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨37,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12254 ⟨37,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨37,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell38 :
    0 ≤ cap12254 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨38,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12254 ⟨38,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨38,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell39 :
    0 ≤ cap12254 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨39,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12254 ⟨39,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨39,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell40 :
    0 ≤ cap12254 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨40,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12254 ⟨40,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨40,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell41 :
    0 ≤ cap12254 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨41,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12254 ⟨41,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨41,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cell42 :
    0 ≤ cap12254 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12254 (parameters ⟨42,by decide⟩)
      (scalarRow12254.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12254 ⟨42,by decide⟩ ∧
    (scalarRow12254.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 ⟨42,by decide⟩ + (scalarRow12254.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12254.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12254.targetFrame := by
  norm_num [cap12254, scalarRow12254, sourceIndex, cell12254, BstLean.Part263.envelope, parameters]

theorem repair12254Cells (j : Fin 43) :
    0 ≤ cap12254 j ∧
    BstLean.Part263.envelope 12254 (parameters j) (scalarRow12254.table (sourceIndex j)).upper ≤ cap12254 j ∧
    (scalarRow12254.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12254 j + (scalarRow12254.table (sourceIndex j)).centre) /
      (scalarRow12254.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12254.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12254Cell0
  | ⟨1,_⟩ => exact repair12254Cell1
  | ⟨2,_⟩ => exact repair12254Cell2
  | ⟨3,_⟩ => exact repair12254Cell3
  | ⟨4,_⟩ => exact repair12254Cell4
  | ⟨5,_⟩ => exact repair12254Cell5
  | ⟨6,_⟩ => exact repair12254Cell6
  | ⟨7,_⟩ => exact repair12254Cell7
  | ⟨8,_⟩ => exact repair12254Cell8
  | ⟨9,_⟩ => exact repair12254Cell9
  | ⟨10,_⟩ => exact repair12254Cell10
  | ⟨11,_⟩ => exact repair12254Cell11
  | ⟨12,_⟩ => exact repair12254Cell12
  | ⟨13,_⟩ => exact repair12254Cell13
  | ⟨14,_⟩ => exact repair12254Cell14
  | ⟨15,_⟩ => exact repair12254Cell15
  | ⟨16,_⟩ => exact repair12254Cell16
  | ⟨17,_⟩ => exact repair12254Cell17
  | ⟨18,_⟩ => exact repair12254Cell18
  | ⟨19,_⟩ => exact repair12254Cell19
  | ⟨20,_⟩ => exact repair12254Cell20
  | ⟨21,_⟩ => exact repair12254Cell21
  | ⟨22,_⟩ => exact repair12254Cell22
  | ⟨23,_⟩ => exact repair12254Cell23
  | ⟨24,_⟩ => exact repair12254Cell24
  | ⟨25,_⟩ => exact repair12254Cell25
  | ⟨26,_⟩ => exact repair12254Cell26
  | ⟨27,_⟩ => exact repair12254Cell27
  | ⟨28,_⟩ => exact repair12254Cell28
  | ⟨29,_⟩ => exact repair12254Cell29
  | ⟨30,_⟩ => exact repair12254Cell30
  | ⟨31,_⟩ => exact repair12254Cell31
  | ⟨32,_⟩ => exact repair12254Cell32
  | ⟨33,_⟩ => exact repair12254Cell33
  | ⟨34,_⟩ => exact repair12254Cell34
  | ⟨35,_⟩ => exact repair12254Cell35
  | ⟨36,_⟩ => exact repair12254Cell36
  | ⟨37,_⟩ => exact repair12254Cell37
  | ⟨38,_⟩ => exact repair12254Cell38
  | ⟨39,_⟩ => exact repair12254Cell39
  | ⟨40,_⟩ => exact repair12254Cell40
  | ⟨41,_⟩ => exact repair12254Cell41
  | ⟨42,_⟩ => exact repair12254Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12254 : FrameRepair 12254 scalarRow12254 where
  cap := cap12254
  cap_nonneg := fun j => (repair12254Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12254])
  endpoint := fun j => (repair12254Cells j).2.1
  endpoint_upper := fun j => (repair12254Cells j).2.2.1
  frame := fun j => (repair12254Cells j).2.2.2

noncomputable def cap12255 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275950457 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276353533 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (55351123 / 200000000 : ℝ)
  | ⟨3,_⟩ => (277156699 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (34694599 / 125000000 : ℝ)
  | ⟨5,_⟩ => (55591179 / 200000000 : ℝ)
  | ⟨6,_⟩ => (2174637 / 7812500 : ℝ)
  | ⟨7,_⟩ => (278750671 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279146829 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55908403 / 200000000 : ℝ)
  | ⟨10,_⟩ => (279936229 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56065799 / 200000000 : ℝ)
  | ⟨12,_⟩ => (140360641 / 500000000 : ℝ)
  | ⟨13,_⟩ => (140556061 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140751447 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140946283 / 500000000 : ℝ)
  | ⟨16,_⟩ => (56456259 / 200000000 : ℝ)
  | ⟨17,_⟩ => (70667273 / 250000000 : ℝ)
  | ⟨18,_⟩ => (283055949 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283441877 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141913439 / 500000000 : ℝ)
  | ⟨21,_⟩ => (142105481 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284594121 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284975869 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71339301 / 250000000 : ℝ)
  | ⟨25,_⟩ => (285737177 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143058373 / 500000000 : ℝ)
  | ⟨27,_⟩ => (143247457 / 500000000 : ℝ)
  | ⟨28,_⟩ => (143436093 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287248561 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287623543 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (14399907 / 50000000 : ℝ)
  | ⟨32,_⟩ => (57674371 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288744179 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72278907 / 250000000 : ℝ)
  | ⟨35,_⟩ => (57897241 / 200000000 : ℝ)
  | ⟨36,_⟩ => (57971181 / 200000000 : ℝ)
  | ⟨37,_⟩ => (58044949 / 200000000 : ℝ)
  | ⟨38,_⟩ => (290592719 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290959321 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291325063 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291689953 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292053991 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12255Cell0 :
    0 ≤ cap12255 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨0,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12255 ⟨0,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨0,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell1 :
    0 ≤ cap12255 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨1,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12255 ⟨1,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨1,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell2 :
    0 ≤ cap12255 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨2,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12255 ⟨2,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨2,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell3 :
    0 ≤ cap12255 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨3,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12255 ⟨3,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨3,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell4 :
    0 ≤ cap12255 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨4,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12255 ⟨4,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨4,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell5 :
    0 ≤ cap12255 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨5,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12255 ⟨5,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨5,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell6 :
    0 ≤ cap12255 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨6,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12255 ⟨6,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨6,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell7 :
    0 ≤ cap12255 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨7,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12255 ⟨7,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨7,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell8 :
    0 ≤ cap12255 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨8,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12255 ⟨8,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨8,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell9 :
    0 ≤ cap12255 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨9,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12255 ⟨9,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨9,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell10 :
    0 ≤ cap12255 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨10,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12255 ⟨10,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨10,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell11 :
    0 ≤ cap12255 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨11,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12255 ⟨11,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨11,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell12 :
    0 ≤ cap12255 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨12,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12255 ⟨12,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨12,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell13 :
    0 ≤ cap12255 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨13,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12255 ⟨13,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨13,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell14 :
    0 ≤ cap12255 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨14,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12255 ⟨14,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨14,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell15 :
    0 ≤ cap12255 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨15,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12255 ⟨15,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨15,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell16 :
    0 ≤ cap12255 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨16,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12255 ⟨16,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨16,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell17 :
    0 ≤ cap12255 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨17,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12255 ⟨17,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨17,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell18 :
    0 ≤ cap12255 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨18,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12255 ⟨18,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨18,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell19 :
    0 ≤ cap12255 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨19,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12255 ⟨19,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨19,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell20 :
    0 ≤ cap12255 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨20,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12255 ⟨20,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨20,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell21 :
    0 ≤ cap12255 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨21,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12255 ⟨21,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨21,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell22 :
    0 ≤ cap12255 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨22,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12255 ⟨22,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨22,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell23 :
    0 ≤ cap12255 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨23,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12255 ⟨23,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨23,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell24 :
    0 ≤ cap12255 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨24,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12255 ⟨24,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨24,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell25 :
    0 ≤ cap12255 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨25,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12255 ⟨25,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨25,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell26 :
    0 ≤ cap12255 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨26,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12255 ⟨26,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨26,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell27 :
    0 ≤ cap12255 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨27,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12255 ⟨27,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨27,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell28 :
    0 ≤ cap12255 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨28,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12255 ⟨28,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨28,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell29 :
    0 ≤ cap12255 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨29,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12255 ⟨29,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨29,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell30 :
    0 ≤ cap12255 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨30,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12255 ⟨30,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨30,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell31 :
    0 ≤ cap12255 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨31,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12255 ⟨31,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨31,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell32 :
    0 ≤ cap12255 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨32,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12255 ⟨32,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨32,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell33 :
    0 ≤ cap12255 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨33,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12255 ⟨33,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨33,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell34 :
    0 ≤ cap12255 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨34,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12255 ⟨34,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨34,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell35 :
    0 ≤ cap12255 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨35,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12255 ⟨35,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨35,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell36 :
    0 ≤ cap12255 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨36,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12255 ⟨36,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨36,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell37 :
    0 ≤ cap12255 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨37,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12255 ⟨37,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨37,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell38 :
    0 ≤ cap12255 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨38,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12255 ⟨38,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨38,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell39 :
    0 ≤ cap12255 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨39,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12255 ⟨39,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨39,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell40 :
    0 ≤ cap12255 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨40,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12255 ⟨40,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨40,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell41 :
    0 ≤ cap12255 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨41,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12255 ⟨41,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨41,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cell42 :
    0 ≤ cap12255 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12255 (parameters ⟨42,by decide⟩)
      (scalarRow12255.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12255 ⟨42,by decide⟩ ∧
    (scalarRow12255.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 ⟨42,by decide⟩ + (scalarRow12255.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12255.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12255.targetFrame := by
  norm_num [cap12255, scalarRow12255, sourceIndex, cell12255, BstLean.Part263.envelope, parameters]

theorem repair12255Cells (j : Fin 43) :
    0 ≤ cap12255 j ∧
    BstLean.Part263.envelope 12255 (parameters j) (scalarRow12255.table (sourceIndex j)).upper ≤ cap12255 j ∧
    (scalarRow12255.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12255 j + (scalarRow12255.table (sourceIndex j)).centre) /
      (scalarRow12255.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12255.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12255Cell0
  | ⟨1,_⟩ => exact repair12255Cell1
  | ⟨2,_⟩ => exact repair12255Cell2
  | ⟨3,_⟩ => exact repair12255Cell3
  | ⟨4,_⟩ => exact repair12255Cell4
  | ⟨5,_⟩ => exact repair12255Cell5
  | ⟨6,_⟩ => exact repair12255Cell6
  | ⟨7,_⟩ => exact repair12255Cell7
  | ⟨8,_⟩ => exact repair12255Cell8
  | ⟨9,_⟩ => exact repair12255Cell9
  | ⟨10,_⟩ => exact repair12255Cell10
  | ⟨11,_⟩ => exact repair12255Cell11
  | ⟨12,_⟩ => exact repair12255Cell12
  | ⟨13,_⟩ => exact repair12255Cell13
  | ⟨14,_⟩ => exact repair12255Cell14
  | ⟨15,_⟩ => exact repair12255Cell15
  | ⟨16,_⟩ => exact repair12255Cell16
  | ⟨17,_⟩ => exact repair12255Cell17
  | ⟨18,_⟩ => exact repair12255Cell18
  | ⟨19,_⟩ => exact repair12255Cell19
  | ⟨20,_⟩ => exact repair12255Cell20
  | ⟨21,_⟩ => exact repair12255Cell21
  | ⟨22,_⟩ => exact repair12255Cell22
  | ⟨23,_⟩ => exact repair12255Cell23
  | ⟨24,_⟩ => exact repair12255Cell24
  | ⟨25,_⟩ => exact repair12255Cell25
  | ⟨26,_⟩ => exact repair12255Cell26
  | ⟨27,_⟩ => exact repair12255Cell27
  | ⟨28,_⟩ => exact repair12255Cell28
  | ⟨29,_⟩ => exact repair12255Cell29
  | ⟨30,_⟩ => exact repair12255Cell30
  | ⟨31,_⟩ => exact repair12255Cell31
  | ⟨32,_⟩ => exact repair12255Cell32
  | ⟨33,_⟩ => exact repair12255Cell33
  | ⟨34,_⟩ => exact repair12255Cell34
  | ⟨35,_⟩ => exact repair12255Cell35
  | ⟨36,_⟩ => exact repair12255Cell36
  | ⟨37,_⟩ => exact repair12255Cell37
  | ⟨38,_⟩ => exact repair12255Cell38
  | ⟨39,_⟩ => exact repair12255Cell39
  | ⟨40,_⟩ => exact repair12255Cell40
  | ⟨41,_⟩ => exact repair12255Cell41
  | ⟨42,_⟩ => exact repair12255Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12255 : FrameRepair 12255 scalarRow12255 where
  cap := cap12255
  cap_nonneg := fun j => (repair12255Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12255])
  endpoint := fun j => (repair12255Cells j).2.1
  endpoint_upper := fun j => (repair12255Cells j).2.2.1
  frame := fun j => (repair12255Cells j).2.2.2

noncomputable def cap12256 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275950381 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276353451 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138377763 / 500000000 : ℝ)
  | ⟨3,_⟩ => (69289151 / 250000000 : ℝ)
  | ⟨4,_⟩ => (27755669 / 100000000 : ℝ)
  | ⟨5,_⟩ => (277955787 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139176711 / 500000000 : ℝ)
  | ⟨7,_⟩ => (5575011 / 20000000 : ℝ)
  | ⟨8,_⟩ => (139573351 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279541881 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279936089 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (17520553 / 62500000 : ℝ)
  | ⟨12,_⟩ => (280721129 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140555981 / 500000000 : ℝ)
  | ⟨14,_⟩ => (35187841 / 125000000 : ℝ)
  | ⟨15,_⟩ => (140946197 / 500000000 : ℝ)
  | ⟨16,_⟩ => (282281117 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282668907 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141527879 / 500000000 : ℝ)
  | ⟨19,_⟩ => (3543021 / 12500000 : ℝ)
  | ⟨20,_⟩ => (11353067 / 40000000 : ℝ)
  | ⟨21,_⟩ => (4440793 / 15625000 : ℝ)
  | ⟨22,_⟩ => (56918781 / 200000000 : ℝ)
  | ⟨23,_⟩ => (284975647 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (17834811 / 62500000 : ℝ)
  | ⟨25,_⟩ => (285736943 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (57223301 / 200000000 : ℝ)
  | ⟨27,_⟩ => (71623667 / 250000000 : ℝ)
  | ⟨28,_⟩ => (286871933 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287248303 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143811639 / 500000000 : ℝ)
  | ⟨31,_⟩ => (71999467 / 250000000 : ℝ)
  | ⟨32,_⟩ => (144185789 / 500000000 : ℝ)
  | ⟨33,_⟩ => (36092987 / 125000000 : ℝ)
  | ⟨34,_⟩ => (289115339 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (28948591 / 100000000 : ℝ)
  | ⟨36,_⟩ => (72463901 / 250000000 : ℝ)
  | ⟨37,_⟩ => (290224437 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145296203 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290959001 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291324737 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291689621 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292053653 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12256Cell0 :
    0 ≤ cap12256 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨0,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12256 ⟨0,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨0,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell1 :
    0 ≤ cap12256 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨1,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12256 ⟨1,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨1,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell2 :
    0 ≤ cap12256 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨2,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12256 ⟨2,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨2,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell3 :
    0 ≤ cap12256 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨3,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12256 ⟨3,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨3,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell4 :
    0 ≤ cap12256 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨4,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12256 ⟨4,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨4,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell5 :
    0 ≤ cap12256 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨5,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12256 ⟨5,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨5,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell6 :
    0 ≤ cap12256 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨6,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12256 ⟨6,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨6,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell7 :
    0 ≤ cap12256 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨7,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12256 ⟨7,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨7,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell8 :
    0 ≤ cap12256 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨8,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12256 ⟨8,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨8,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell9 :
    0 ≤ cap12256 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨9,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12256 ⟨9,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨9,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell10 :
    0 ≤ cap12256 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨10,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12256 ⟨10,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨10,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell11 :
    0 ≤ cap12256 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨11,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12256 ⟨11,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨11,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell12 :
    0 ≤ cap12256 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨12,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12256 ⟨12,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨12,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell13 :
    0 ≤ cap12256 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨13,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12256 ⟨13,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨13,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell14 :
    0 ≤ cap12256 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨14,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12256 ⟨14,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨14,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell15 :
    0 ≤ cap12256 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨15,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12256 ⟨15,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨15,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell16 :
    0 ≤ cap12256 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨16,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12256 ⟨16,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨16,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell17 :
    0 ≤ cap12256 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨17,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12256 ⟨17,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨17,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell18 :
    0 ≤ cap12256 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨18,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12256 ⟨18,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨18,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell19 :
    0 ≤ cap12256 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨19,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12256 ⟨19,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨19,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell20 :
    0 ≤ cap12256 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨20,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12256 ⟨20,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨20,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell21 :
    0 ≤ cap12256 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨21,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12256 ⟨21,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨21,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell22 :
    0 ≤ cap12256 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨22,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12256 ⟨22,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨22,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell23 :
    0 ≤ cap12256 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨23,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12256 ⟨23,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨23,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell24 :
    0 ≤ cap12256 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨24,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12256 ⟨24,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨24,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell25 :
    0 ≤ cap12256 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨25,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12256 ⟨25,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨25,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell26 :
    0 ≤ cap12256 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨26,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12256 ⟨26,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨26,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell27 :
    0 ≤ cap12256 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨27,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12256 ⟨27,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨27,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell28 :
    0 ≤ cap12256 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨28,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12256 ⟨28,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨28,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell29 :
    0 ≤ cap12256 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨29,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12256 ⟨29,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨29,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell30 :
    0 ≤ cap12256 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨30,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12256 ⟨30,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨30,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell31 :
    0 ≤ cap12256 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨31,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12256 ⟨31,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨31,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell32 :
    0 ≤ cap12256 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨32,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12256 ⟨32,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨32,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell33 :
    0 ≤ cap12256 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨33,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12256 ⟨33,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨33,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell34 :
    0 ≤ cap12256 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨34,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12256 ⟨34,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨34,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell35 :
    0 ≤ cap12256 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨35,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12256 ⟨35,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨35,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell36 :
    0 ≤ cap12256 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨36,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12256 ⟨36,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨36,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell37 :
    0 ≤ cap12256 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨37,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12256 ⟨37,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨37,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell38 :
    0 ≤ cap12256 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨38,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12256 ⟨38,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨38,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell39 :
    0 ≤ cap12256 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨39,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12256 ⟨39,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨39,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell40 :
    0 ≤ cap12256 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨40,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12256 ⟨40,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨40,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell41 :
    0 ≤ cap12256 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨41,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12256 ⟨41,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨41,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cell42 :
    0 ≤ cap12256 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12256 (parameters ⟨42,by decide⟩)
      (scalarRow12256.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12256 ⟨42,by decide⟩ ∧
    (scalarRow12256.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 ⟨42,by decide⟩ + (scalarRow12256.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12256.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12256.targetFrame := by
  norm_num [cap12256, scalarRow12256, sourceIndex, cell12256, BstLean.Part263.envelope, parameters]

theorem repair12256Cells (j : Fin 43) :
    0 ≤ cap12256 j ∧
    BstLean.Part263.envelope 12256 (parameters j) (scalarRow12256.table (sourceIndex j)).upper ≤ cap12256 j ∧
    (scalarRow12256.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12256 j + (scalarRow12256.table (sourceIndex j)).centre) /
      (scalarRow12256.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12256.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12256Cell0
  | ⟨1,_⟩ => exact repair12256Cell1
  | ⟨2,_⟩ => exact repair12256Cell2
  | ⟨3,_⟩ => exact repair12256Cell3
  | ⟨4,_⟩ => exact repair12256Cell4
  | ⟨5,_⟩ => exact repair12256Cell5
  | ⟨6,_⟩ => exact repair12256Cell6
  | ⟨7,_⟩ => exact repair12256Cell7
  | ⟨8,_⟩ => exact repair12256Cell8
  | ⟨9,_⟩ => exact repair12256Cell9
  | ⟨10,_⟩ => exact repair12256Cell10
  | ⟨11,_⟩ => exact repair12256Cell11
  | ⟨12,_⟩ => exact repair12256Cell12
  | ⟨13,_⟩ => exact repair12256Cell13
  | ⟨14,_⟩ => exact repair12256Cell14
  | ⟨15,_⟩ => exact repair12256Cell15
  | ⟨16,_⟩ => exact repair12256Cell16
  | ⟨17,_⟩ => exact repair12256Cell17
  | ⟨18,_⟩ => exact repair12256Cell18
  | ⟨19,_⟩ => exact repair12256Cell19
  | ⟨20,_⟩ => exact repair12256Cell20
  | ⟨21,_⟩ => exact repair12256Cell21
  | ⟨22,_⟩ => exact repair12256Cell22
  | ⟨23,_⟩ => exact repair12256Cell23
  | ⟨24,_⟩ => exact repair12256Cell24
  | ⟨25,_⟩ => exact repair12256Cell25
  | ⟨26,_⟩ => exact repair12256Cell26
  | ⟨27,_⟩ => exact repair12256Cell27
  | ⟨28,_⟩ => exact repair12256Cell28
  | ⟨29,_⟩ => exact repair12256Cell29
  | ⟨30,_⟩ => exact repair12256Cell30
  | ⟨31,_⟩ => exact repair12256Cell31
  | ⟨32,_⟩ => exact repair12256Cell32
  | ⟨33,_⟩ => exact repair12256Cell33
  | ⟨34,_⟩ => exact repair12256Cell34
  | ⟨35,_⟩ => exact repair12256Cell35
  | ⟨36,_⟩ => exact repair12256Cell36
  | ⟨37,_⟩ => exact repair12256Cell37
  | ⟨38,_⟩ => exact repair12256Cell38
  | ⟨39,_⟩ => exact repair12256Cell39
  | ⟨40,_⟩ => exact repair12256Cell40
  | ⟨41,_⟩ => exact repair12256Cell41
  | ⟨42,_⟩ => exact repair12256Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12256 : FrameRepair 12256 scalarRow12256 where
  cap := cap12256
  cap_nonneg := fun j => (repair12256Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12256])
  endpoint := fun j => (repair12256Cells j).2.1
  endpoint_upper := fun j => (repair12256Cells j).2.2.1
  frame := fun j => (repair12256Cells j).2.2.2

noncomputable def cap12257 : Fin 43 → ℝ
  | ⟨0,_⟩ => (55190061 / 200000000 : ℝ)
  | ⟨1,_⟩ => (276353369 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138377719 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277156509 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277556589 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277955679 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278353307 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278750429 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139573287 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279541747 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279935949 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140164351 / 500000000 : ℝ)
  | ⟨12,_⟩ => (17545061 / 62500000 : ℝ)
  | ⟨13,_⟩ => (281111803 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281502563 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (140946111 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141140469 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282668723 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283055567 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283441483 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283826471 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284210543 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (28459369 / 100000000 : ℝ)
  | ⟨23,_⟩ => (11399017 / 40000000 : ℝ)
  | ⟨24,_⟩ => (71339187 / 250000000 : ℝ)
  | ⟨25,_⟩ => (285736709 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (57223253 / 200000000 : ℝ)
  | ⟨27,_⟩ => (286494421 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286871681 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (71812011 / 250000000 : ℝ)
  | ⟨30,_⟩ => (287623013 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287997597 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (2883713 / 10000000 : ℝ)
  | ⟨33,_⟩ => (288743613 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (5782301 / 20000000 : ℝ)
  | ⟨35,_⟩ => (57897123 / 200000000 : ℝ)
  | ⟨36,_⟩ => (144927651 / 500000000 : ℝ)
  | ⟨37,_⟩ => (29022413 / 100000000 : ℝ)
  | ⟨38,_⟩ => (72648023 / 250000000 : ℝ)
  | ⟨39,_⟩ => (145479341 / 500000000 : ℝ)
  | ⟨40,_⟩ => (72831103 / 250000000 : ℝ)
  | ⟨41,_⟩ => (29168929 / 100000000 : ℝ)
  | ⟨42,_⟩ => (73013329 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12257Cell0 :
    0 ≤ cap12257 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨0,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12257 ⟨0,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨0,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell1 :
    0 ≤ cap12257 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨1,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12257 ⟨1,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨1,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell2 :
    0 ≤ cap12257 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨2,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12257 ⟨2,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨2,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell3 :
    0 ≤ cap12257 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨3,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12257 ⟨3,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨3,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell4 :
    0 ≤ cap12257 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨4,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12257 ⟨4,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨4,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell5 :
    0 ≤ cap12257 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨5,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12257 ⟨5,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨5,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell6 :
    0 ≤ cap12257 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨6,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12257 ⟨6,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨6,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell7 :
    0 ≤ cap12257 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨7,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12257 ⟨7,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨7,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell8 :
    0 ≤ cap12257 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨8,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12257 ⟨8,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨8,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell9 :
    0 ≤ cap12257 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨9,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12257 ⟨9,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨9,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell10 :
    0 ≤ cap12257 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨10,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12257 ⟨10,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨10,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell11 :
    0 ≤ cap12257 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨11,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12257 ⟨11,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨11,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell12 :
    0 ≤ cap12257 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨12,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12257 ⟨12,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨12,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell13 :
    0 ≤ cap12257 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨13,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12257 ⟨13,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨13,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell14 :
    0 ≤ cap12257 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨14,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12257 ⟨14,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨14,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell15 :
    0 ≤ cap12257 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨15,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12257 ⟨15,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨15,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell16 :
    0 ≤ cap12257 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨16,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12257 ⟨16,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨16,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell17 :
    0 ≤ cap12257 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨17,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12257 ⟨17,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨17,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell18 :
    0 ≤ cap12257 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨18,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12257 ⟨18,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨18,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell19 :
    0 ≤ cap12257 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨19,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12257 ⟨19,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨19,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell20 :
    0 ≤ cap12257 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨20,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12257 ⟨20,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨20,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell21 :
    0 ≤ cap12257 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨21,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12257 ⟨21,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨21,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell22 :
    0 ≤ cap12257 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨22,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12257 ⟨22,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨22,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell23 :
    0 ≤ cap12257 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨23,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12257 ⟨23,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨23,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell24 :
    0 ≤ cap12257 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨24,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12257 ⟨24,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨24,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell25 :
    0 ≤ cap12257 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨25,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12257 ⟨25,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨25,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell26 :
    0 ≤ cap12257 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨26,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12257 ⟨26,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨26,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell27 :
    0 ≤ cap12257 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨27,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12257 ⟨27,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨27,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell28 :
    0 ≤ cap12257 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨28,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12257 ⟨28,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨28,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell29 :
    0 ≤ cap12257 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨29,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12257 ⟨29,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨29,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell30 :
    0 ≤ cap12257 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨30,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12257 ⟨30,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨30,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell31 :
    0 ≤ cap12257 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨31,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12257 ⟨31,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨31,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell32 :
    0 ≤ cap12257 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨32,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12257 ⟨32,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨32,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell33 :
    0 ≤ cap12257 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨33,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12257 ⟨33,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨33,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell34 :
    0 ≤ cap12257 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨34,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12257 ⟨34,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨34,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell35 :
    0 ≤ cap12257 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨35,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12257 ⟨35,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨35,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell36 :
    0 ≤ cap12257 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨36,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12257 ⟨36,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨36,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell37 :
    0 ≤ cap12257 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨37,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12257 ⟨37,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨37,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell38 :
    0 ≤ cap12257 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨38,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12257 ⟨38,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨38,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell39 :
    0 ≤ cap12257 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨39,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12257 ⟨39,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨39,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell40 :
    0 ≤ cap12257 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨40,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12257 ⟨40,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨40,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell41 :
    0 ≤ cap12257 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨41,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12257 ⟨41,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨41,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cell42 :
    0 ≤ cap12257 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12257 (parameters ⟨42,by decide⟩)
      (scalarRow12257.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12257 ⟨42,by decide⟩ ∧
    (scalarRow12257.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 ⟨42,by decide⟩ + (scalarRow12257.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12257.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12257.targetFrame := by
  norm_num [cap12257, scalarRow12257, sourceIndex, cell12257, BstLean.Part263.envelope, parameters]

theorem repair12257Cells (j : Fin 43) :
    0 ≤ cap12257 j ∧
    BstLean.Part263.envelope 12257 (parameters j) (scalarRow12257.table (sourceIndex j)).upper ≤ cap12257 j ∧
    (scalarRow12257.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12257 j + (scalarRow12257.table (sourceIndex j)).centre) /
      (scalarRow12257.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12257.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12257Cell0
  | ⟨1,_⟩ => exact repair12257Cell1
  | ⟨2,_⟩ => exact repair12257Cell2
  | ⟨3,_⟩ => exact repair12257Cell3
  | ⟨4,_⟩ => exact repair12257Cell4
  | ⟨5,_⟩ => exact repair12257Cell5
  | ⟨6,_⟩ => exact repair12257Cell6
  | ⟨7,_⟩ => exact repair12257Cell7
  | ⟨8,_⟩ => exact repair12257Cell8
  | ⟨9,_⟩ => exact repair12257Cell9
  | ⟨10,_⟩ => exact repair12257Cell10
  | ⟨11,_⟩ => exact repair12257Cell11
  | ⟨12,_⟩ => exact repair12257Cell12
  | ⟨13,_⟩ => exact repair12257Cell13
  | ⟨14,_⟩ => exact repair12257Cell14
  | ⟨15,_⟩ => exact repair12257Cell15
  | ⟨16,_⟩ => exact repair12257Cell16
  | ⟨17,_⟩ => exact repair12257Cell17
  | ⟨18,_⟩ => exact repair12257Cell18
  | ⟨19,_⟩ => exact repair12257Cell19
  | ⟨20,_⟩ => exact repair12257Cell20
  | ⟨21,_⟩ => exact repair12257Cell21
  | ⟨22,_⟩ => exact repair12257Cell22
  | ⟨23,_⟩ => exact repair12257Cell23
  | ⟨24,_⟩ => exact repair12257Cell24
  | ⟨25,_⟩ => exact repair12257Cell25
  | ⟨26,_⟩ => exact repair12257Cell26
  | ⟨27,_⟩ => exact repair12257Cell27
  | ⟨28,_⟩ => exact repair12257Cell28
  | ⟨29,_⟩ => exact repair12257Cell29
  | ⟨30,_⟩ => exact repair12257Cell30
  | ⟨31,_⟩ => exact repair12257Cell31
  | ⟨32,_⟩ => exact repair12257Cell32
  | ⟨33,_⟩ => exact repair12257Cell33
  | ⟨34,_⟩ => exact repair12257Cell34
  | ⟨35,_⟩ => exact repair12257Cell35
  | ⟨36,_⟩ => exact repair12257Cell36
  | ⟨37,_⟩ => exact repair12257Cell37
  | ⟨38,_⟩ => exact repair12257Cell38
  | ⟨39,_⟩ => exact repair12257Cell39
  | ⟨40,_⟩ => exact repair12257Cell40
  | ⟨41,_⟩ => exact repair12257Cell41
  | ⟨42,_⟩ => exact repair12257Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12257 : FrameRepair 12257 scalarRow12257 where
  cap := cap12257
  cap_nonneg := fun j => (repair12257Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12257])
  endpoint := fun j => (repair12257Cells j).2.1
  endpoint_upper := fun j => (repair12257Cells j).2.2.1
  frame := fun j => (repair12257Cells j).2.2.2

noncomputable def cap12258 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275950229 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (138176643 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276755349 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277156413 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277556487 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (27795557 / 100000000 : ℝ)
  | ⟨6,_⟩ => (34794149 / 125000000 : ℝ)
  | ⟨7,_⟩ => (69687577 / 250000000 : ℝ)
  | ⟨8,_⟩ => (279146447 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139770807 / 500000000 : ℝ)
  | ⟨10,_⟩ => (279935809 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56065711 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280720823 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (70277911 / 250000000 : ℝ)
  | ⟨14,_⟩ => (281502397 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (5637841 / 20000000 : ℝ)
  | ⟨16,_⟩ => (7057019 / 25000000 : ℝ)
  | ⟨17,_⟩ => (141334269 / 500000000 : ℝ)
  | ⟨18,_⟩ => (283055377 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141720643 / 500000000 : ℝ)
  | ⟨20,_⟩ => (70956567 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284210333 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (142296737 / 500000000 : ℝ)
  | ⟨23,_⟩ => (284975203 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (7133913 / 25000000 : ℝ)
  | ⟨25,_⟩ => (11429459 / 40000000 : ℝ)
  | ⟨26,_⟩ => (11444641 / 40000000 : ℝ)
  | ⟨27,_⟩ => (11459767 / 40000000 : ℝ)
  | ⟨28,_⟩ => (71717857 / 250000000 : ℝ)
  | ⟨29,_⟩ => (57449557 / 200000000 : ℝ)
  | ⟨30,_⟩ => (71905687 / 250000000 : ℝ)
  | ⟨31,_⟩ => (143998663 / 500000000 : ℝ)
  | ⟨32,_⟩ => (288371023 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (28874333 / 100000000 : ℝ)
  | ⟨34,_⟩ => (289114761 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289485319 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289855001 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290223823 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290591779 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145479181 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145662043 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291688959 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292052979 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12258Cell0 :
    0 ≤ cap12258 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨0,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12258 ⟨0,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨0,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell1 :
    0 ≤ cap12258 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨1,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12258 ⟨1,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨1,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell2 :
    0 ≤ cap12258 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨2,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12258 ⟨2,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨2,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell3 :
    0 ≤ cap12258 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨3,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12258 ⟨3,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨3,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell4 :
    0 ≤ cap12258 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨4,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12258 ⟨4,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨4,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell5 :
    0 ≤ cap12258 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨5,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12258 ⟨5,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨5,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell6 :
    0 ≤ cap12258 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨6,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12258 ⟨6,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨6,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell7 :
    0 ≤ cap12258 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨7,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12258 ⟨7,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨7,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell8 :
    0 ≤ cap12258 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨8,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12258 ⟨8,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨8,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell9 :
    0 ≤ cap12258 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨9,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12258 ⟨9,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨9,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell10 :
    0 ≤ cap12258 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨10,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12258 ⟨10,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨10,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell11 :
    0 ≤ cap12258 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨11,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12258 ⟨11,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨11,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell12 :
    0 ≤ cap12258 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨12,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12258 ⟨12,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨12,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell13 :
    0 ≤ cap12258 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨13,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12258 ⟨13,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨13,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell14 :
    0 ≤ cap12258 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨14,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12258 ⟨14,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨14,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell15 :
    0 ≤ cap12258 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨15,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12258 ⟨15,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨15,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell16 :
    0 ≤ cap12258 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨16,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12258 ⟨16,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨16,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell17 :
    0 ≤ cap12258 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨17,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12258 ⟨17,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨17,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell18 :
    0 ≤ cap12258 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨18,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12258 ⟨18,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨18,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell19 :
    0 ≤ cap12258 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨19,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12258 ⟨19,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨19,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell20 :
    0 ≤ cap12258 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨20,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12258 ⟨20,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨20,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell21 :
    0 ≤ cap12258 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨21,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12258 ⟨21,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨21,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell22 :
    0 ≤ cap12258 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨22,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12258 ⟨22,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨22,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell23 :
    0 ≤ cap12258 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨23,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12258 ⟨23,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨23,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell24 :
    0 ≤ cap12258 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨24,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12258 ⟨24,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨24,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell25 :
    0 ≤ cap12258 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨25,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12258 ⟨25,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨25,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell26 :
    0 ≤ cap12258 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨26,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12258 ⟨26,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨26,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell27 :
    0 ≤ cap12258 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨27,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12258 ⟨27,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨27,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell28 :
    0 ≤ cap12258 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨28,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12258 ⟨28,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨28,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell29 :
    0 ≤ cap12258 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨29,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12258 ⟨29,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨29,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell30 :
    0 ≤ cap12258 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨30,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12258 ⟨30,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨30,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell31 :
    0 ≤ cap12258 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨31,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12258 ⟨31,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨31,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell32 :
    0 ≤ cap12258 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨32,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12258 ⟨32,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨32,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell33 :
    0 ≤ cap12258 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨33,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12258 ⟨33,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨33,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell34 :
    0 ≤ cap12258 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨34,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12258 ⟨34,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨34,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell35 :
    0 ≤ cap12258 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨35,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12258 ⟨35,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨35,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell36 :
    0 ≤ cap12258 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨36,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12258 ⟨36,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨36,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell37 :
    0 ≤ cap12258 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨37,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12258 ⟨37,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨37,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell38 :
    0 ≤ cap12258 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨38,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12258 ⟨38,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨38,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell39 :
    0 ≤ cap12258 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨39,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12258 ⟨39,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨39,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell40 :
    0 ≤ cap12258 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨40,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12258 ⟨40,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨40,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell41 :
    0 ≤ cap12258 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨41,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12258 ⟨41,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨41,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cell42 :
    0 ≤ cap12258 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12258 (parameters ⟨42,by decide⟩)
      (scalarRow12258.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12258 ⟨42,by decide⟩ ∧
    (scalarRow12258.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 ⟨42,by decide⟩ + (scalarRow12258.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12258.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12258.targetFrame := by
  norm_num [cap12258, scalarRow12258, sourceIndex, cell12258, BstLean.Part263.envelope, parameters]

theorem repair12258Cells (j : Fin 43) :
    0 ≤ cap12258 j ∧
    BstLean.Part263.envelope 12258 (parameters j) (scalarRow12258.table (sourceIndex j)).upper ≤ cap12258 j ∧
    (scalarRow12258.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12258 j + (scalarRow12258.table (sourceIndex j)).centre) /
      (scalarRow12258.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12258.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12258Cell0
  | ⟨1,_⟩ => exact repair12258Cell1
  | ⟨2,_⟩ => exact repair12258Cell2
  | ⟨3,_⟩ => exact repair12258Cell3
  | ⟨4,_⟩ => exact repair12258Cell4
  | ⟨5,_⟩ => exact repair12258Cell5
  | ⟨6,_⟩ => exact repair12258Cell6
  | ⟨7,_⟩ => exact repair12258Cell7
  | ⟨8,_⟩ => exact repair12258Cell8
  | ⟨9,_⟩ => exact repair12258Cell9
  | ⟨10,_⟩ => exact repair12258Cell10
  | ⟨11,_⟩ => exact repair12258Cell11
  | ⟨12,_⟩ => exact repair12258Cell12
  | ⟨13,_⟩ => exact repair12258Cell13
  | ⟨14,_⟩ => exact repair12258Cell14
  | ⟨15,_⟩ => exact repair12258Cell15
  | ⟨16,_⟩ => exact repair12258Cell16
  | ⟨17,_⟩ => exact repair12258Cell17
  | ⟨18,_⟩ => exact repair12258Cell18
  | ⟨19,_⟩ => exact repair12258Cell19
  | ⟨20,_⟩ => exact repair12258Cell20
  | ⟨21,_⟩ => exact repair12258Cell21
  | ⟨22,_⟩ => exact repair12258Cell22
  | ⟨23,_⟩ => exact repair12258Cell23
  | ⟨24,_⟩ => exact repair12258Cell24
  | ⟨25,_⟩ => exact repair12258Cell25
  | ⟨26,_⟩ => exact repair12258Cell26
  | ⟨27,_⟩ => exact repair12258Cell27
  | ⟨28,_⟩ => exact repair12258Cell28
  | ⟨29,_⟩ => exact repair12258Cell29
  | ⟨30,_⟩ => exact repair12258Cell30
  | ⟨31,_⟩ => exact repair12258Cell31
  | ⟨32,_⟩ => exact repair12258Cell32
  | ⟨33,_⟩ => exact repair12258Cell33
  | ⟨34,_⟩ => exact repair12258Cell34
  | ⟨35,_⟩ => exact repair12258Cell35
  | ⟨36,_⟩ => exact repair12258Cell36
  | ⟨37,_⟩ => exact repair12258Cell37
  | ⟨38,_⟩ => exact repair12258Cell38
  | ⟨39,_⟩ => exact repair12258Cell39
  | ⟨40,_⟩ => exact repair12258Cell40
  | ⟨41,_⟩ => exact repair12258Cell41
  | ⟨42,_⟩ => exact repair12258Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12258 : FrameRepair 12258 scalarRow12258 where
  cap := cap12258
  cap_nonneg := fun j => (repair12258Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12258])
  endpoint := fun j => (repair12258Cells j).2.1
  endpoint_upper := fun j => (repair12258Cells j).2.2.1
  frame := fun j => (repair12258Cells j).2.2.2

noncomputable def cap12259 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975077 / 500000000 : ℝ)
  | ⟨1,_⟩ => (69088301 / 250000000 : ℝ)
  | ⟨2,_⟩ => (13837763 / 50000000 : ℝ)
  | ⟨3,_⟩ => (138578159 / 500000000 : ℝ)
  | ⟨4,_⟩ => (55511277 / 200000000 : ℝ)
  | ⟨5,_⟩ => (138977731 / 500000000 : ℝ)
  | ⟨6,_⟩ => (139176539 / 500000000 : ℝ)
  | ⟨7,_⟩ => (278750187 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (3489329 / 12500000 : ℝ)
  | ⟨9,_⟩ => (6988537 / 25000000 : ℝ)
  | ⟨10,_⟩ => (279935669 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280328409 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (28072067 / 100000000 : ℝ)
  | ⟨13,_⟩ => (56222297 / 200000000 : ℝ)
  | ⟨14,_⟩ => (35187779 / 125000000 : ℝ)
  | ⟨15,_⟩ => (281891879 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (141140291 / 500000000 : ℝ)
  | ⟨17,_⟩ => (141334177 / 500000000 : ℝ)
  | ⟨18,_⟩ => (141527593 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283441089 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (56765213 / 200000000 : ℝ)
  | ⟨21,_⟩ => (71052531 / 250000000 : ℝ)
  | ⟨22,_⟩ => (142296629 / 500000000 : ℝ)
  | ⟨23,_⟩ => (142487491 / 500000000 : ℝ)
  | ⟨24,_⟩ => (71339073 / 250000000 : ℝ)
  | ⟨25,_⟩ => (3571703 / 12500000 : ℝ)
  | ⟨26,_⟩ => (35764473 / 125000000 : ℝ)
  | ⟨27,_⟩ => (35811741 / 125000000 : ℝ)
  | ⟨28,_⟩ => (11474847 / 40000000 : ℝ)
  | ⟨29,_⟩ => (143623763 / 500000000 : ℝ)
  | ⟨30,_⟩ => (287622483 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (57599411 / 200000000 : ℝ)
  | ⟨32,_⟩ => (144185373 / 500000000 : ℝ)
  | ⟨33,_⟩ => (288743047 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289114471 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (9046407 / 31250000 : ℝ)
  | ⟨36,_⟩ => (2898547 / 10000000 : ℝ)
  | ⟨37,_⟩ => (58044703 / 200000000 : ℝ)
  | ⟨38,_⟩ => (145295733 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290958043 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291323761 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291688627 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292052641 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12259Cell0 :
    0 ≤ cap12259 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨0,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12259 ⟨0,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨0,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell1 :
    0 ≤ cap12259 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨1,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12259 ⟨1,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨1,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell2 :
    0 ≤ cap12259 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨2,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12259 ⟨2,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨2,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell3 :
    0 ≤ cap12259 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨3,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12259 ⟨3,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨3,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell4 :
    0 ≤ cap12259 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨4,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12259 ⟨4,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨4,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell5 :
    0 ≤ cap12259 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨5,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12259 ⟨5,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨5,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell6 :
    0 ≤ cap12259 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨6,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12259 ⟨6,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨6,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell7 :
    0 ≤ cap12259 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨7,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12259 ⟨7,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨7,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell8 :
    0 ≤ cap12259 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨8,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12259 ⟨8,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨8,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell9 :
    0 ≤ cap12259 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨9,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12259 ⟨9,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨9,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell10 :
    0 ≤ cap12259 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨10,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12259 ⟨10,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨10,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell11 :
    0 ≤ cap12259 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨11,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12259 ⟨11,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨11,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell12 :
    0 ≤ cap12259 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨12,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12259 ⟨12,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨12,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell13 :
    0 ≤ cap12259 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨13,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12259 ⟨13,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨13,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell14 :
    0 ≤ cap12259 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨14,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12259 ⟨14,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨14,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell15 :
    0 ≤ cap12259 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨15,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12259 ⟨15,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨15,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell16 :
    0 ≤ cap12259 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨16,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12259 ⟨16,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨16,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell17 :
    0 ≤ cap12259 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨17,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12259 ⟨17,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨17,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell18 :
    0 ≤ cap12259 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨18,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12259 ⟨18,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨18,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell19 :
    0 ≤ cap12259 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨19,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12259 ⟨19,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨19,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell20 :
    0 ≤ cap12259 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨20,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12259 ⟨20,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨20,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell21 :
    0 ≤ cap12259 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨21,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12259 ⟨21,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨21,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell22 :
    0 ≤ cap12259 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨22,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12259 ⟨22,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨22,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell23 :
    0 ≤ cap12259 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨23,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12259 ⟨23,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨23,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell24 :
    0 ≤ cap12259 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨24,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12259 ⟨24,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨24,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell25 :
    0 ≤ cap12259 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨25,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12259 ⟨25,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨25,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell26 :
    0 ≤ cap12259 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨26,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12259 ⟨26,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨26,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell27 :
    0 ≤ cap12259 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨27,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12259 ⟨27,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨27,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell28 :
    0 ≤ cap12259 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨28,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12259 ⟨28,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨28,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell29 :
    0 ≤ cap12259 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨29,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12259 ⟨29,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨29,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell30 :
    0 ≤ cap12259 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨30,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12259 ⟨30,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨30,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell31 :
    0 ≤ cap12259 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨31,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12259 ⟨31,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨31,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell32 :
    0 ≤ cap12259 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨32,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12259 ⟨32,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨32,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell33 :
    0 ≤ cap12259 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨33,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12259 ⟨33,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨33,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell34 :
    0 ≤ cap12259 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨34,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12259 ⟨34,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨34,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell35 :
    0 ≤ cap12259 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨35,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12259 ⟨35,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨35,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell36 :
    0 ≤ cap12259 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨36,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12259 ⟨36,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨36,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell37 :
    0 ≤ cap12259 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨37,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12259 ⟨37,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨37,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell38 :
    0 ≤ cap12259 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨38,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12259 ⟨38,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨38,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell39 :
    0 ≤ cap12259 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨39,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12259 ⟨39,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨39,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell40 :
    0 ≤ cap12259 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨40,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12259 ⟨40,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨40,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell41 :
    0 ≤ cap12259 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨41,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12259 ⟨41,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨41,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cell42 :
    0 ≤ cap12259 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12259 (parameters ⟨42,by decide⟩)
      (scalarRow12259.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12259 ⟨42,by decide⟩ ∧
    (scalarRow12259.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 ⟨42,by decide⟩ + (scalarRow12259.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12259.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12259.targetFrame := by
  norm_num [cap12259, scalarRow12259, sourceIndex, cell12259, BstLean.Part263.envelope, parameters]

theorem repair12259Cells (j : Fin 43) :
    0 ≤ cap12259 j ∧
    BstLean.Part263.envelope 12259 (parameters j) (scalarRow12259.table (sourceIndex j)).upper ≤ cap12259 j ∧
    (scalarRow12259.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12259 j + (scalarRow12259.table (sourceIndex j)).centre) /
      (scalarRow12259.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12259.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12259Cell0
  | ⟨1,_⟩ => exact repair12259Cell1
  | ⟨2,_⟩ => exact repair12259Cell2
  | ⟨3,_⟩ => exact repair12259Cell3
  | ⟨4,_⟩ => exact repair12259Cell4
  | ⟨5,_⟩ => exact repair12259Cell5
  | ⟨6,_⟩ => exact repair12259Cell6
  | ⟨7,_⟩ => exact repair12259Cell7
  | ⟨8,_⟩ => exact repair12259Cell8
  | ⟨9,_⟩ => exact repair12259Cell9
  | ⟨10,_⟩ => exact repair12259Cell10
  | ⟨11,_⟩ => exact repair12259Cell11
  | ⟨12,_⟩ => exact repair12259Cell12
  | ⟨13,_⟩ => exact repair12259Cell13
  | ⟨14,_⟩ => exact repair12259Cell14
  | ⟨15,_⟩ => exact repair12259Cell15
  | ⟨16,_⟩ => exact repair12259Cell16
  | ⟨17,_⟩ => exact repair12259Cell17
  | ⟨18,_⟩ => exact repair12259Cell18
  | ⟨19,_⟩ => exact repair12259Cell19
  | ⟨20,_⟩ => exact repair12259Cell20
  | ⟨21,_⟩ => exact repair12259Cell21
  | ⟨22,_⟩ => exact repair12259Cell22
  | ⟨23,_⟩ => exact repair12259Cell23
  | ⟨24,_⟩ => exact repair12259Cell24
  | ⟨25,_⟩ => exact repair12259Cell25
  | ⟨26,_⟩ => exact repair12259Cell26
  | ⟨27,_⟩ => exact repair12259Cell27
  | ⟨28,_⟩ => exact repair12259Cell28
  | ⟨29,_⟩ => exact repair12259Cell29
  | ⟨30,_⟩ => exact repair12259Cell30
  | ⟨31,_⟩ => exact repair12259Cell31
  | ⟨32,_⟩ => exact repair12259Cell32
  | ⟨33,_⟩ => exact repair12259Cell33
  | ⟨34,_⟩ => exact repair12259Cell34
  | ⟨35,_⟩ => exact repair12259Cell35
  | ⟨36,_⟩ => exact repair12259Cell36
  | ⟨37,_⟩ => exact repair12259Cell37
  | ⟨38,_⟩ => exact repair12259Cell38
  | ⟨39,_⟩ => exact repair12259Cell39
  | ⟨40,_⟩ => exact repair12259Cell40
  | ⟨41,_⟩ => exact repair12259Cell41
  | ⟨42,_⟩ => exact repair12259Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12259 : FrameRepair 12259 scalarRow12259 where
  cap := cap12259
  cap_nonneg := fun j => (repair12259Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12259])
  endpoint := fun j => (repair12259Cells j).2.1
  endpoint_upper := fun j => (repair12259Cells j).2.2.1
  frame := fun j => (repair12259Cells j).2.2.2

noncomputable def cap12260 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975039 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138176561 / 500000000 : ℝ)
  | ⟨2,_⟩ => (69188793 / 250000000 : ℝ)
  | ⟨3,_⟩ => (277156223 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (69389071 / 250000000 : ℝ)
  | ⟨5,_⟩ => (138977677 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278352963 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139375033 / 500000000 : ℝ)
  | ⟨8,_⟩ => (17446637 / 62500000 : ℝ)
  | ⟨9,_⟩ => (139770673 / 500000000 : ℝ)
  | ⟨10,_⟩ => (34991941 / 125000000 : ℝ)
  | ⟨11,_⟩ => (140164131 / 500000000 : ℝ)
  | ⟨12,_⟩ => (140360259 / 500000000 : ℝ)
  | ⟨13,_⟩ => (140555663 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140751033 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281891707 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (70570101 / 250000000 : ℝ)
  | ⟨17,_⟩ => (28266817 / 100000000 : ℝ)
  | ⟨18,_⟩ => (70763749 / 250000000 : ℝ)
  | ⟨19,_⟩ => (283440893 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (141912931 / 500000000 : ℝ)
  | ⟨21,_⟩ => (142104957 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284593043 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (7124369 / 25000000 : ℝ)
  | ⟨24,_⟩ => (8917377 / 31250000 : ℝ)
  | ⟨25,_⟩ => (142868003 / 500000000 : ℝ)
  | ⟨26,_⟩ => (35764443 / 125000000 : ℝ)
  | ⟨27,_⟩ => (143246841 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286870923 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287247267 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143811109 / 500000000 : ℝ)
  | ⟨31,_⟩ => (17999799 / 62500000 : ℝ)
  | ⟨32,_⟩ => (288370469 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288742763 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144557091 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289484729 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144927199 / 500000000 : ℝ)
  | ⟨37,_⟩ => (36277901 / 125000000 : ℝ)
  | ⟨38,_⟩ => (18161947 / 62500000 : ℝ)
  | ⟨39,_⟩ => (72739431 / 250000000 : ℝ)
  | ⟨40,_⟩ => (72830859 / 250000000 : ℝ)
  | ⟨41,_⟩ => (36461037 / 125000000 : ℝ)
  | ⟨42,_⟩ => (18253269 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12260Cell0 :
    0 ≤ cap12260 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨0,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12260 ⟨0,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨0,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell1 :
    0 ≤ cap12260 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨1,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12260 ⟨1,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨1,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell2 :
    0 ≤ cap12260 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨2,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12260 ⟨2,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨2,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell3 :
    0 ≤ cap12260 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨3,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12260 ⟨3,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨3,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell4 :
    0 ≤ cap12260 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨4,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12260 ⟨4,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨4,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell5 :
    0 ≤ cap12260 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨5,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12260 ⟨5,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨5,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell6 :
    0 ≤ cap12260 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨6,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12260 ⟨6,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨6,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell7 :
    0 ≤ cap12260 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨7,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12260 ⟨7,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨7,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell8 :
    0 ≤ cap12260 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨8,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12260 ⟨8,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨8,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell9 :
    0 ≤ cap12260 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨9,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12260 ⟨9,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨9,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell10 :
    0 ≤ cap12260 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨10,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12260 ⟨10,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨10,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell11 :
    0 ≤ cap12260 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨11,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12260 ⟨11,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨11,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell12 :
    0 ≤ cap12260 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨12,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12260 ⟨12,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨12,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell13 :
    0 ≤ cap12260 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨13,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12260 ⟨13,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨13,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell14 :
    0 ≤ cap12260 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨14,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12260 ⟨14,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨14,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell15 :
    0 ≤ cap12260 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨15,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12260 ⟨15,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨15,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell16 :
    0 ≤ cap12260 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨16,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12260 ⟨16,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨16,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell17 :
    0 ≤ cap12260 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨17,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12260 ⟨17,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨17,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell18 :
    0 ≤ cap12260 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨18,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12260 ⟨18,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨18,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell19 :
    0 ≤ cap12260 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨19,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12260 ⟨19,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨19,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell20 :
    0 ≤ cap12260 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨20,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12260 ⟨20,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨20,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell21 :
    0 ≤ cap12260 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨21,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12260 ⟨21,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨21,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell22 :
    0 ≤ cap12260 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨22,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12260 ⟨22,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨22,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell23 :
    0 ≤ cap12260 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨23,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12260 ⟨23,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨23,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell24 :
    0 ≤ cap12260 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨24,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12260 ⟨24,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨24,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell25 :
    0 ≤ cap12260 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨25,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12260 ⟨25,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨25,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell26 :
    0 ≤ cap12260 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨26,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12260 ⟨26,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨26,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell27 :
    0 ≤ cap12260 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨27,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12260 ⟨27,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨27,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell28 :
    0 ≤ cap12260 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨28,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12260 ⟨28,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨28,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell29 :
    0 ≤ cap12260 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨29,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12260 ⟨29,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨29,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell30 :
    0 ≤ cap12260 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨30,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12260 ⟨30,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨30,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell31 :
    0 ≤ cap12260 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨31,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12260 ⟨31,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨31,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell32 :
    0 ≤ cap12260 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨32,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12260 ⟨32,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨32,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell33 :
    0 ≤ cap12260 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨33,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12260 ⟨33,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨33,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell34 :
    0 ≤ cap12260 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨34,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12260 ⟨34,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨34,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell35 :
    0 ≤ cap12260 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨35,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12260 ⟨35,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨35,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell36 :
    0 ≤ cap12260 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨36,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12260 ⟨36,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨36,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell37 :
    0 ≤ cap12260 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨37,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12260 ⟨37,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨37,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell38 :
    0 ≤ cap12260 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨38,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12260 ⟨38,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨38,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell39 :
    0 ≤ cap12260 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨39,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12260 ⟨39,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨39,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell40 :
    0 ≤ cap12260 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨40,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12260 ⟨40,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨40,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell41 :
    0 ≤ cap12260 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨41,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12260 ⟨41,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨41,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cell42 :
    0 ≤ cap12260 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12260 (parameters ⟨42,by decide⟩)
      (scalarRow12260.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12260 ⟨42,by decide⟩ ∧
    (scalarRow12260.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 ⟨42,by decide⟩ + (scalarRow12260.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12260.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12260.targetFrame := by
  norm_num [cap12260, scalarRow12260, sourceIndex, cell12260, BstLean.Part263.envelope, parameters]

theorem repair12260Cells (j : Fin 43) :
    0 ≤ cap12260 j ∧
    BstLean.Part263.envelope 12260 (parameters j) (scalarRow12260.table (sourceIndex j)).upper ≤ cap12260 j ∧
    (scalarRow12260.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12260 j + (scalarRow12260.table (sourceIndex j)).centre) /
      (scalarRow12260.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12260.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12260Cell0
  | ⟨1,_⟩ => exact repair12260Cell1
  | ⟨2,_⟩ => exact repair12260Cell2
  | ⟨3,_⟩ => exact repair12260Cell3
  | ⟨4,_⟩ => exact repair12260Cell4
  | ⟨5,_⟩ => exact repair12260Cell5
  | ⟨6,_⟩ => exact repair12260Cell6
  | ⟨7,_⟩ => exact repair12260Cell7
  | ⟨8,_⟩ => exact repair12260Cell8
  | ⟨9,_⟩ => exact repair12260Cell9
  | ⟨10,_⟩ => exact repair12260Cell10
  | ⟨11,_⟩ => exact repair12260Cell11
  | ⟨12,_⟩ => exact repair12260Cell12
  | ⟨13,_⟩ => exact repair12260Cell13
  | ⟨14,_⟩ => exact repair12260Cell14
  | ⟨15,_⟩ => exact repair12260Cell15
  | ⟨16,_⟩ => exact repair12260Cell16
  | ⟨17,_⟩ => exact repair12260Cell17
  | ⟨18,_⟩ => exact repair12260Cell18
  | ⟨19,_⟩ => exact repair12260Cell19
  | ⟨20,_⟩ => exact repair12260Cell20
  | ⟨21,_⟩ => exact repair12260Cell21
  | ⟨22,_⟩ => exact repair12260Cell22
  | ⟨23,_⟩ => exact repair12260Cell23
  | ⟨24,_⟩ => exact repair12260Cell24
  | ⟨25,_⟩ => exact repair12260Cell25
  | ⟨26,_⟩ => exact repair12260Cell26
  | ⟨27,_⟩ => exact repair12260Cell27
  | ⟨28,_⟩ => exact repair12260Cell28
  | ⟨29,_⟩ => exact repair12260Cell29
  | ⟨30,_⟩ => exact repair12260Cell30
  | ⟨31,_⟩ => exact repair12260Cell31
  | ⟨32,_⟩ => exact repair12260Cell32
  | ⟨33,_⟩ => exact repair12260Cell33
  | ⟨34,_⟩ => exact repair12260Cell34
  | ⟨35,_⟩ => exact repair12260Cell35
  | ⟨36,_⟩ => exact repair12260Cell36
  | ⟨37,_⟩ => exact repair12260Cell37
  | ⟨38,_⟩ => exact repair12260Cell38
  | ⟨39,_⟩ => exact repair12260Cell39
  | ⟨40,_⟩ => exact repair12260Cell40
  | ⟨41,_⟩ => exact repair12260Cell41
  | ⟨42,_⟩ => exact repair12260Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12260 : FrameRepair 12260 scalarRow12260 where
  cap := cap12260
  cap_nonneg := fun j => (repair12260Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12260])
  endpoint := fun j => (repair12260Cells j).2.1
  endpoint_upper := fun j => (repair12260Cells j).2.2.1
  frame := fun j => (repair12260Cells j).2.2.2

noncomputable def cap12261 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137975001 / 500000000 : ℝ)
  | ⟨1,_⟩ => (3454413 / 12500000 : ℝ)
  | ⟨2,_⟩ => (276755083 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (8661129 / 31250000 : ℝ)
  | ⟨4,_⟩ => (138778091 / 500000000 : ℝ)
  | ⟨5,_⟩ => (138977623 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278352849 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (55749989 / 200000000 : ℝ)
  | ⟨8,_⟩ => (55829213 / 200000000 : ℝ)
  | ⟨9,_⟩ => (69885303 / 250000000 : ℝ)
  | ⟨10,_⟩ => (69983847 / 250000000 : ℝ)
  | ⟨11,_⟩ => (70082029 / 250000000 : ℝ)
  | ⟨12,_⟩ => (56144073 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281111167 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281501901 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (56378307 / 200000000 : ℝ)
  | ⟨16,_⟩ => (141140113 / 500000000 : ℝ)
  | ⟨17,_⟩ => (56533597 / 200000000 : ℝ)
  | ⟨18,_⟩ => (56610961 / 200000000 : ℝ)
  | ⟨19,_⟩ => (35430087 / 125000000 : ℝ)
  | ⟨20,_⟩ => (283825659 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56841941 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284592827 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142487269 / 500000000 : ℝ)
  | ⟨24,_⟩ => (71338959 / 250000000 : ℝ)
  | ⟨25,_⟩ => (71433943 / 250000000 : ℝ)
  | ⟨26,_⟩ => (35764413 / 125000000 : ℝ)
  | ⟨27,_⟩ => (57298687 / 200000000 : ℝ)
  | ⟨28,_⟩ => (28687067 / 100000000 : ℝ)
  | ⟨29,_⟩ => (287247009 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287621953 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143998257 / 500000000 : ℝ)
  | ⟨32,_⟩ => (18023137 / 62500000 : ℝ)
  | ⟨33,_⟩ => (3609281 / 12500000 : ℝ)
  | ⟨34,_⟩ => (289113893 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (144742217 / 500000000 : ℝ)
  | ⟨36,_⟩ => (289854097 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290222901 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290590839 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (58191481 / 200000000 : ℝ)
  | ⟨40,_⟩ => (291323111 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (58337593 / 200000000 : ℝ)
  | ⟨42,_⟩ => (292051967 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12261Cell0 :
    0 ≤ cap12261 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨0,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12261 ⟨0,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨0,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell1 :
    0 ≤ cap12261 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨1,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12261 ⟨1,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨1,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell2 :
    0 ≤ cap12261 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨2,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12261 ⟨2,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨2,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell3 :
    0 ≤ cap12261 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨3,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12261 ⟨3,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨3,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell4 :
    0 ≤ cap12261 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨4,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12261 ⟨4,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨4,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell5 :
    0 ≤ cap12261 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨5,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12261 ⟨5,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨5,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell6 :
    0 ≤ cap12261 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨6,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12261 ⟨6,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨6,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell7 :
    0 ≤ cap12261 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨7,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12261 ⟨7,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨7,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell8 :
    0 ≤ cap12261 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨8,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12261 ⟨8,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨8,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell9 :
    0 ≤ cap12261 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨9,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12261 ⟨9,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨9,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell10 :
    0 ≤ cap12261 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨10,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12261 ⟨10,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨10,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell11 :
    0 ≤ cap12261 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨11,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12261 ⟨11,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨11,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell12 :
    0 ≤ cap12261 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨12,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12261 ⟨12,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨12,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell13 :
    0 ≤ cap12261 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨13,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12261 ⟨13,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨13,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell14 :
    0 ≤ cap12261 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨14,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12261 ⟨14,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨14,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell15 :
    0 ≤ cap12261 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨15,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12261 ⟨15,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨15,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell16 :
    0 ≤ cap12261 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨16,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12261 ⟨16,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨16,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell17 :
    0 ≤ cap12261 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨17,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12261 ⟨17,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨17,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell18 :
    0 ≤ cap12261 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨18,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12261 ⟨18,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨18,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell19 :
    0 ≤ cap12261 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨19,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12261 ⟨19,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨19,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell20 :
    0 ≤ cap12261 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨20,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12261 ⟨20,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨20,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell21 :
    0 ≤ cap12261 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨21,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12261 ⟨21,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨21,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell22 :
    0 ≤ cap12261 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨22,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12261 ⟨22,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨22,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell23 :
    0 ≤ cap12261 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨23,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12261 ⟨23,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨23,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell24 :
    0 ≤ cap12261 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨24,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12261 ⟨24,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨24,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell25 :
    0 ≤ cap12261 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨25,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12261 ⟨25,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨25,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell26 :
    0 ≤ cap12261 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨26,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12261 ⟨26,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨26,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell27 :
    0 ≤ cap12261 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨27,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12261 ⟨27,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨27,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell28 :
    0 ≤ cap12261 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨28,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12261 ⟨28,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨28,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell29 :
    0 ≤ cap12261 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨29,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12261 ⟨29,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨29,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell30 :
    0 ≤ cap12261 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨30,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12261 ⟨30,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨30,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell31 :
    0 ≤ cap12261 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨31,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12261 ⟨31,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨31,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell32 :
    0 ≤ cap12261 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨32,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12261 ⟨32,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨32,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell33 :
    0 ≤ cap12261 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨33,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12261 ⟨33,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨33,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell34 :
    0 ≤ cap12261 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨34,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12261 ⟨34,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨34,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell35 :
    0 ≤ cap12261 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨35,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12261 ⟨35,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨35,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell36 :
    0 ≤ cap12261 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨36,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12261 ⟨36,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨36,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell37 :
    0 ≤ cap12261 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨37,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12261 ⟨37,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨37,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell38 :
    0 ≤ cap12261 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨38,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12261 ⟨38,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨38,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell39 :
    0 ≤ cap12261 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨39,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12261 ⟨39,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨39,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell40 :
    0 ≤ cap12261 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨40,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12261 ⟨40,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨40,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell41 :
    0 ≤ cap12261 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨41,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12261 ⟨41,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨41,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cell42 :
    0 ≤ cap12261 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12261 (parameters ⟨42,by decide⟩)
      (scalarRow12261.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12261 ⟨42,by decide⟩ ∧
    (scalarRow12261.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 ⟨42,by decide⟩ + (scalarRow12261.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12261.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12261.targetFrame := by
  norm_num [cap12261, scalarRow12261, sourceIndex, cell12261, BstLean.Part263.envelope, parameters]

theorem repair12261Cells (j : Fin 43) :
    0 ≤ cap12261 j ∧
    BstLean.Part263.envelope 12261 (parameters j) (scalarRow12261.table (sourceIndex j)).upper ≤ cap12261 j ∧
    (scalarRow12261.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12261 j + (scalarRow12261.table (sourceIndex j)).centre) /
      (scalarRow12261.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12261.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12261Cell0
  | ⟨1,_⟩ => exact repair12261Cell1
  | ⟨2,_⟩ => exact repair12261Cell2
  | ⟨3,_⟩ => exact repair12261Cell3
  | ⟨4,_⟩ => exact repair12261Cell4
  | ⟨5,_⟩ => exact repair12261Cell5
  | ⟨6,_⟩ => exact repair12261Cell6
  | ⟨7,_⟩ => exact repair12261Cell7
  | ⟨8,_⟩ => exact repair12261Cell8
  | ⟨9,_⟩ => exact repair12261Cell9
  | ⟨10,_⟩ => exact repair12261Cell10
  | ⟨11,_⟩ => exact repair12261Cell11
  | ⟨12,_⟩ => exact repair12261Cell12
  | ⟨13,_⟩ => exact repair12261Cell13
  | ⟨14,_⟩ => exact repair12261Cell14
  | ⟨15,_⟩ => exact repair12261Cell15
  | ⟨16,_⟩ => exact repair12261Cell16
  | ⟨17,_⟩ => exact repair12261Cell17
  | ⟨18,_⟩ => exact repair12261Cell18
  | ⟨19,_⟩ => exact repair12261Cell19
  | ⟨20,_⟩ => exact repair12261Cell20
  | ⟨21,_⟩ => exact repair12261Cell21
  | ⟨22,_⟩ => exact repair12261Cell22
  | ⟨23,_⟩ => exact repair12261Cell23
  | ⟨24,_⟩ => exact repair12261Cell24
  | ⟨25,_⟩ => exact repair12261Cell25
  | ⟨26,_⟩ => exact repair12261Cell26
  | ⟨27,_⟩ => exact repair12261Cell27
  | ⟨28,_⟩ => exact repair12261Cell28
  | ⟨29,_⟩ => exact repair12261Cell29
  | ⟨30,_⟩ => exact repair12261Cell30
  | ⟨31,_⟩ => exact repair12261Cell31
  | ⟨32,_⟩ => exact repair12261Cell32
  | ⟨33,_⟩ => exact repair12261Cell33
  | ⟨34,_⟩ => exact repair12261Cell34
  | ⟨35,_⟩ => exact repair12261Cell35
  | ⟨36,_⟩ => exact repair12261Cell36
  | ⟨37,_⟩ => exact repair12261Cell37
  | ⟨38,_⟩ => exact repair12261Cell38
  | ⟨39,_⟩ => exact repair12261Cell39
  | ⟨40,_⟩ => exact repair12261Cell40
  | ⟨41,_⟩ => exact repair12261Cell41
  | ⟨42,_⟩ => exact repair12261Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12261 : FrameRepair 12261 scalarRow12261 where
  cap := cap12261
  cap_nonneg := fun j => (repair12261Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12261])
  endpoint := fun j => (repair12261Cells j).2.1
  endpoint_upper := fun j => (repair12261Cells j).2.2.1
  frame := fun j => (repair12261Cells j).2.2.2

noncomputable def cap12262 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137974963 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138176479 / 500000000 : ℝ)
  | ⟨2,_⟩ => (138377497 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277156033 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277556081 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138977569 / 500000000 : ℝ)
  | ⟨6,_⟩ => (139176367 / 500000000 : ℝ)
  | ⟨7,_⟩ => (2177733 / 7812500 : ℝ)
  | ⟨8,_⟩ => (139572969 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279541079 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (17495953 / 62500000 : ℝ)
  | ⟨11,_⟩ => (280327969 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (70180053 / 250000000 : ℝ)
  | ⟨13,_⟩ => (8784719 / 31250000 : ℝ)
  | ⟨14,_⟩ => (56300347 / 200000000 : ℝ)
  | ⟨15,_⟩ => (281891363 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (17642503 / 62500000 : ℝ)
  | ⟨17,_⟩ => (282667801 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (141527307 / 500000000 : ℝ)
  | ⟨19,_⟩ => (283440499 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (17739091 / 62500000 : ℝ)
  | ⟨21,_⟩ => (35526187 / 125000000 : ℝ)
  | ⟨22,_⟩ => (71148153 / 250000000 : ℝ)
  | ⟨23,_⟩ => (71243579 / 250000000 : ℝ)
  | ⟨24,_⟩ => (35669451 / 125000000 : ℝ)
  | ⟨25,_⟩ => (142867769 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286115063 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286493189 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143435209 / 500000000 : ℝ)
  | ⟨29,_⟩ => (1148987 / 4000000 : ℝ)
  | ⟨30,_⟩ => (287621689 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287996243 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (57673983 / 200000000 : ℝ)
  | ⟨33,_⟩ => (288742197 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (72278401 / 250000000 : ℝ)
  | ⟨35,_⟩ => (144742069 / 500000000 : ℝ)
  | ⟨36,_⟩ => (72463449 / 250000000 : ℝ)
  | ⟨37,_⟩ => (145111297 / 500000000 : ℝ)
  | ⟨38,_⟩ => (145295263 / 500000000 : ℝ)
  | ⟨39,_⟩ => (58191417 / 200000000 : ℝ)
  | ⟨40,_⟩ => (58264557 / 200000000 : ℝ)
  | ⟨41,_⟩ => (145843817 / 500000000 : ℝ)
  | ⟨42,_⟩ => (29205163 / 100000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12262Cell0 :
    0 ≤ cap12262 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨0,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12262 ⟨0,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨0,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell1 :
    0 ≤ cap12262 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨1,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12262 ⟨1,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨1,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell2 :
    0 ≤ cap12262 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨2,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12262 ⟨2,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨2,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell3 :
    0 ≤ cap12262 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨3,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12262 ⟨3,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨3,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell4 :
    0 ≤ cap12262 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨4,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12262 ⟨4,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨4,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell5 :
    0 ≤ cap12262 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨5,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12262 ⟨5,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨5,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell6 :
    0 ≤ cap12262 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨6,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12262 ⟨6,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨6,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell7 :
    0 ≤ cap12262 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨7,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12262 ⟨7,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨7,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell8 :
    0 ≤ cap12262 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨8,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12262 ⟨8,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨8,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell9 :
    0 ≤ cap12262 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨9,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12262 ⟨9,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨9,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell10 :
    0 ≤ cap12262 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨10,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12262 ⟨10,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨10,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell11 :
    0 ≤ cap12262 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨11,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12262 ⟨11,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨11,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell12 :
    0 ≤ cap12262 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨12,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12262 ⟨12,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨12,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell13 :
    0 ≤ cap12262 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨13,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12262 ⟨13,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨13,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell14 :
    0 ≤ cap12262 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨14,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12262 ⟨14,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨14,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell15 :
    0 ≤ cap12262 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨15,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12262 ⟨15,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨15,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell16 :
    0 ≤ cap12262 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨16,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12262 ⟨16,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨16,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell17 :
    0 ≤ cap12262 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨17,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12262 ⟨17,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨17,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell18 :
    0 ≤ cap12262 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨18,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12262 ⟨18,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨18,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell19 :
    0 ≤ cap12262 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨19,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12262 ⟨19,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨19,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell20 :
    0 ≤ cap12262 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨20,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12262 ⟨20,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨20,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell21 :
    0 ≤ cap12262 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨21,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12262 ⟨21,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨21,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell22 :
    0 ≤ cap12262 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨22,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12262 ⟨22,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨22,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell23 :
    0 ≤ cap12262 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨23,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12262 ⟨23,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨23,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell24 :
    0 ≤ cap12262 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨24,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12262 ⟨24,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨24,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell25 :
    0 ≤ cap12262 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨25,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12262 ⟨25,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨25,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell26 :
    0 ≤ cap12262 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨26,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12262 ⟨26,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨26,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell27 :
    0 ≤ cap12262 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨27,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12262 ⟨27,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨27,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell28 :
    0 ≤ cap12262 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨28,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12262 ⟨28,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨28,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell29 :
    0 ≤ cap12262 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨29,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12262 ⟨29,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨29,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell30 :
    0 ≤ cap12262 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨30,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12262 ⟨30,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨30,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell31 :
    0 ≤ cap12262 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨31,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12262 ⟨31,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨31,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell32 :
    0 ≤ cap12262 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨32,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12262 ⟨32,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨32,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell33 :
    0 ≤ cap12262 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨33,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12262 ⟨33,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨33,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell34 :
    0 ≤ cap12262 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨34,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12262 ⟨34,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨34,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell35 :
    0 ≤ cap12262 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨35,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12262 ⟨35,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨35,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell36 :
    0 ≤ cap12262 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨36,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12262 ⟨36,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨36,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell37 :
    0 ≤ cap12262 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨37,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12262 ⟨37,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨37,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell38 :
    0 ≤ cap12262 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨38,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12262 ⟨38,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨38,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell39 :
    0 ≤ cap12262 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨39,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12262 ⟨39,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨39,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell40 :
    0 ≤ cap12262 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨40,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12262 ⟨40,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨40,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell41 :
    0 ≤ cap12262 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨41,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12262 ⟨41,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨41,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cell42 :
    0 ≤ cap12262 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12262 (parameters ⟨42,by decide⟩)
      (scalarRow12262.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12262 ⟨42,by decide⟩ ∧
    (scalarRow12262.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 ⟨42,by decide⟩ + (scalarRow12262.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12262.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12262.targetFrame := by
  norm_num [cap12262, scalarRow12262, sourceIndex, cell12262, BstLean.Part263.envelope, parameters]

theorem repair12262Cells (j : Fin 43) :
    0 ≤ cap12262 j ∧
    BstLean.Part263.envelope 12262 (parameters j) (scalarRow12262.table (sourceIndex j)).upper ≤ cap12262 j ∧
    (scalarRow12262.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12262 j + (scalarRow12262.table (sourceIndex j)).centre) /
      (scalarRow12262.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12262.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12262Cell0
  | ⟨1,_⟩ => exact repair12262Cell1
  | ⟨2,_⟩ => exact repair12262Cell2
  | ⟨3,_⟩ => exact repair12262Cell3
  | ⟨4,_⟩ => exact repair12262Cell4
  | ⟨5,_⟩ => exact repair12262Cell5
  | ⟨6,_⟩ => exact repair12262Cell6
  | ⟨7,_⟩ => exact repair12262Cell7
  | ⟨8,_⟩ => exact repair12262Cell8
  | ⟨9,_⟩ => exact repair12262Cell9
  | ⟨10,_⟩ => exact repair12262Cell10
  | ⟨11,_⟩ => exact repair12262Cell11
  | ⟨12,_⟩ => exact repair12262Cell12
  | ⟨13,_⟩ => exact repair12262Cell13
  | ⟨14,_⟩ => exact repair12262Cell14
  | ⟨15,_⟩ => exact repair12262Cell15
  | ⟨16,_⟩ => exact repair12262Cell16
  | ⟨17,_⟩ => exact repair12262Cell17
  | ⟨18,_⟩ => exact repair12262Cell18
  | ⟨19,_⟩ => exact repair12262Cell19
  | ⟨20,_⟩ => exact repair12262Cell20
  | ⟨21,_⟩ => exact repair12262Cell21
  | ⟨22,_⟩ => exact repair12262Cell22
  | ⟨23,_⟩ => exact repair12262Cell23
  | ⟨24,_⟩ => exact repair12262Cell24
  | ⟨25,_⟩ => exact repair12262Cell25
  | ⟨26,_⟩ => exact repair12262Cell26
  | ⟨27,_⟩ => exact repair12262Cell27
  | ⟨28,_⟩ => exact repair12262Cell28
  | ⟨29,_⟩ => exact repair12262Cell29
  | ⟨30,_⟩ => exact repair12262Cell30
  | ⟨31,_⟩ => exact repair12262Cell31
  | ⟨32,_⟩ => exact repair12262Cell32
  | ⟨33,_⟩ => exact repair12262Cell33
  | ⟨34,_⟩ => exact repair12262Cell34
  | ⟨35,_⟩ => exact repair12262Cell35
  | ⟨36,_⟩ => exact repair12262Cell36
  | ⟨37,_⟩ => exact repair12262Cell37
  | ⟨38,_⟩ => exact repair12262Cell38
  | ⟨39,_⟩ => exact repair12262Cell39
  | ⟨40,_⟩ => exact repair12262Cell40
  | ⟨41,_⟩ => exact repair12262Cell41
  | ⟨42,_⟩ => exact repair12262Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12262 : FrameRepair 12262 scalarRow12262 where
  cap := cap12262
  cap_nonneg := fun j => (repair12262Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12262])
  endpoint := fun j => (repair12262Cells j).2.1
  endpoint_upper := fun j => (repair12262Cells j).2.2.1
  frame := fun j => (repair12262Cells j).2.2.2

noncomputable def cap12263 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275949851 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (2210823 / 8000000 : ℝ)
  | ⟨2,_⟩ => (138377453 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138577969 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277555979 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (27795503 / 100000000 : ℝ)
  | ⟨6,_⟩ => (13917631 / 50000000 : ℝ)
  | ⟨7,_⟩ => (278749703 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279145811 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (55908189 / 200000000 : ℝ)
  | ⟨10,_⟩ => (69983777 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280327823 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280720059 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (4392357 / 15625000 : ℝ)
  | ⟨14,_⟩ => (28150157 / 100000000 : ℝ)
  | ⟨15,_⟩ => (35236399 / 125000000 : ℝ)
  | ⟨16,_⟩ => (28227987 / 100000000 : ℝ)
  | ⟨17,_⟩ => (282667617 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (35381803 / 125000000 : ℝ)
  | ⟨19,_⟩ => (141720151 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283825253 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284209287 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (71148099 / 250000000 : ℝ)
  | ⟨23,_⟩ => (56994819 / 200000000 : ℝ)
  | ⟨24,_⟩ => (14267769 / 50000000 : ℝ)
  | ⟨25,_⟩ => (35716913 / 125000000 : ℝ)
  | ⟨26,_⟩ => (286114823 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143246471 / 500000000 : ℝ)
  | ⟨28,_⟩ => (57374033 / 200000000 : ℝ)
  | ⟨29,_⟩ => (287246491 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (17976339 / 62500000 : ℝ)
  | ⟨31,_⟩ => (71998993 / 250000000 : ℝ)
  | ⟨32,_⟩ => (144184819 / 500000000 : ℝ)
  | ⟨33,_⟩ => (144370957 / 500000000 : ℝ)
  | ⟨34,_⟩ => (57822663 / 200000000 : ℝ)
  | ⟨35,_⟩ => (289483843 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (57970699 / 200000000 : ℝ)
  | ⟨37,_⟩ => (145111143 / 500000000 : ℝ)
  | ⟨38,_⟩ => (290590213 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145478383 / 500000000 : ℝ)
  | ⟨40,_⟩ => (14566123 / 50000000 : ℝ)
  | ⟨41,_⟩ => (291687303 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292051293 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12263Cell0 :
    0 ≤ cap12263 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨0,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12263 ⟨0,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨0,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell1 :
    0 ≤ cap12263 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨1,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12263 ⟨1,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨1,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell2 :
    0 ≤ cap12263 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨2,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12263 ⟨2,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨2,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell3 :
    0 ≤ cap12263 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨3,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12263 ⟨3,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨3,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell4 :
    0 ≤ cap12263 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨4,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12263 ⟨4,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨4,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell5 :
    0 ≤ cap12263 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨5,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12263 ⟨5,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨5,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell6 :
    0 ≤ cap12263 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨6,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12263 ⟨6,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨6,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell7 :
    0 ≤ cap12263 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨7,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12263 ⟨7,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨7,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell8 :
    0 ≤ cap12263 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨8,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12263 ⟨8,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨8,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell9 :
    0 ≤ cap12263 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨9,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12263 ⟨9,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨9,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell10 :
    0 ≤ cap12263 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨10,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12263 ⟨10,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨10,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell11 :
    0 ≤ cap12263 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨11,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12263 ⟨11,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨11,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell12 :
    0 ≤ cap12263 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨12,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12263 ⟨12,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨12,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell13 :
    0 ≤ cap12263 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨13,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12263 ⟨13,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨13,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell14 :
    0 ≤ cap12263 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨14,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12263 ⟨14,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨14,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell15 :
    0 ≤ cap12263 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨15,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12263 ⟨15,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨15,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell16 :
    0 ≤ cap12263 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨16,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12263 ⟨16,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨16,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell17 :
    0 ≤ cap12263 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨17,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12263 ⟨17,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨17,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell18 :
    0 ≤ cap12263 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨18,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12263 ⟨18,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨18,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell19 :
    0 ≤ cap12263 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨19,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12263 ⟨19,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨19,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell20 :
    0 ≤ cap12263 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨20,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12263 ⟨20,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨20,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell21 :
    0 ≤ cap12263 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨21,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12263 ⟨21,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨21,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell22 :
    0 ≤ cap12263 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨22,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12263 ⟨22,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨22,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell23 :
    0 ≤ cap12263 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨23,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12263 ⟨23,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨23,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell24 :
    0 ≤ cap12263 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨24,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12263 ⟨24,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨24,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell25 :
    0 ≤ cap12263 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨25,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12263 ⟨25,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨25,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell26 :
    0 ≤ cap12263 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨26,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12263 ⟨26,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨26,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell27 :
    0 ≤ cap12263 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨27,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12263 ⟨27,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨27,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell28 :
    0 ≤ cap12263 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨28,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12263 ⟨28,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨28,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell29 :
    0 ≤ cap12263 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨29,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12263 ⟨29,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨29,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell30 :
    0 ≤ cap12263 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨30,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12263 ⟨30,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨30,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell31 :
    0 ≤ cap12263 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨31,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12263 ⟨31,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨31,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell32 :
    0 ≤ cap12263 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨32,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12263 ⟨32,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨32,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell33 :
    0 ≤ cap12263 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨33,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12263 ⟨33,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨33,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell34 :
    0 ≤ cap12263 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨34,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12263 ⟨34,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨34,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell35 :
    0 ≤ cap12263 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨35,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12263 ⟨35,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨35,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell36 :
    0 ≤ cap12263 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨36,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12263 ⟨36,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨36,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell37 :
    0 ≤ cap12263 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨37,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12263 ⟨37,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨37,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell38 :
    0 ≤ cap12263 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨38,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12263 ⟨38,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨38,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell39 :
    0 ≤ cap12263 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨39,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12263 ⟨39,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨39,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell40 :
    0 ≤ cap12263 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨40,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12263 ⟨40,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨40,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell41 :
    0 ≤ cap12263 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨41,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12263 ⟨41,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨41,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cell42 :
    0 ≤ cap12263 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12263 (parameters ⟨42,by decide⟩)
      (scalarRow12263.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12263 ⟨42,by decide⟩ ∧
    (scalarRow12263.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 ⟨42,by decide⟩ + (scalarRow12263.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12263.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12263.targetFrame := by
  norm_num [cap12263, scalarRow12263, sourceIndex, cell12263, BstLean.Part263.envelope, parameters]

theorem repair12263Cells (j : Fin 43) :
    0 ≤ cap12263 j ∧
    BstLean.Part263.envelope 12263 (parameters j) (scalarRow12263.table (sourceIndex j)).upper ≤ cap12263 j ∧
    (scalarRow12263.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12263 j + (scalarRow12263.table (sourceIndex j)).centre) /
      (scalarRow12263.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12263.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12263Cell0
  | ⟨1,_⟩ => exact repair12263Cell1
  | ⟨2,_⟩ => exact repair12263Cell2
  | ⟨3,_⟩ => exact repair12263Cell3
  | ⟨4,_⟩ => exact repair12263Cell4
  | ⟨5,_⟩ => exact repair12263Cell5
  | ⟨6,_⟩ => exact repair12263Cell6
  | ⟨7,_⟩ => exact repair12263Cell7
  | ⟨8,_⟩ => exact repair12263Cell8
  | ⟨9,_⟩ => exact repair12263Cell9
  | ⟨10,_⟩ => exact repair12263Cell10
  | ⟨11,_⟩ => exact repair12263Cell11
  | ⟨12,_⟩ => exact repair12263Cell12
  | ⟨13,_⟩ => exact repair12263Cell13
  | ⟨14,_⟩ => exact repair12263Cell14
  | ⟨15,_⟩ => exact repair12263Cell15
  | ⟨16,_⟩ => exact repair12263Cell16
  | ⟨17,_⟩ => exact repair12263Cell17
  | ⟨18,_⟩ => exact repair12263Cell18
  | ⟨19,_⟩ => exact repair12263Cell19
  | ⟨20,_⟩ => exact repair12263Cell20
  | ⟨21,_⟩ => exact repair12263Cell21
  | ⟨22,_⟩ => exact repair12263Cell22
  | ⟨23,_⟩ => exact repair12263Cell23
  | ⟨24,_⟩ => exact repair12263Cell24
  | ⟨25,_⟩ => exact repair12263Cell25
  | ⟨26,_⟩ => exact repair12263Cell26
  | ⟨27,_⟩ => exact repair12263Cell27
  | ⟨28,_⟩ => exact repair12263Cell28
  | ⟨29,_⟩ => exact repair12263Cell29
  | ⟨30,_⟩ => exact repair12263Cell30
  | ⟨31,_⟩ => exact repair12263Cell31
  | ⟨32,_⟩ => exact repair12263Cell32
  | ⟨33,_⟩ => exact repair12263Cell33
  | ⟨34,_⟩ => exact repair12263Cell34
  | ⟨35,_⟩ => exact repair12263Cell35
  | ⟨36,_⟩ => exact repair12263Cell36
  | ⟨37,_⟩ => exact repair12263Cell37
  | ⟨38,_⟩ => exact repair12263Cell38
  | ⟨39,_⟩ => exact repair12263Cell39
  | ⟨40,_⟩ => exact repair12263Cell40
  | ⟨41,_⟩ => exact repair12263Cell41
  | ⟨42,_⟩ => exact repair12263Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12263 : FrameRepair 12263 scalarRow12263 where
  cap := cap12263
  cap_nonneg := fun j => (repair12263Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12263])
  endpoint := fun j => (repair12263Cells j).2.1
  endpoint_upper := fun j => (repair12263Cells j).2.2.1
  frame := fun j => (repair12263Cells j).2.2.2

noncomputable def cap12264 : Fin 43 → ℝ
  | ⟨0,_⟩ => (11037991 / 40000000 : ℝ)
  | ⟨1,_⟩ => (276352793 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276754817 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (138577921 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277555877 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138977461 / 500000000 : ℝ)
  | ⟨6,_⟩ => (139176253 / 500000000 : ℝ)
  | ⟨7,_⟩ => (278749583 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279145683 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279540811 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (34991871 / 125000000 : ℝ)
  | ⟨11,_⟩ => (70081919 / 250000000 : ℝ)
  | ⟨12,_⟩ => (140359953 / 500000000 : ℝ)
  | ⟨13,_⟩ => (281110689 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (56300281 / 200000000 : ℝ)
  | ⟨15,_⟩ => (14094551 / 50000000 : ℝ)
  | ⟨16,_⟩ => (70569923 / 250000000 : ℝ)
  | ⟨17,_⟩ => (35333429 / 125000000 : ℝ)
  | ⟨18,_⟩ => (283054233 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (56688021 / 200000000 : ℝ)
  | ⟨20,_⟩ => (5676501 / 20000000 : ℝ)
  | ⟨21,_⟩ => (284209077 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284592181 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284973873 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (17834697 / 62500000 : ℝ)
  | ⟨25,_⟩ => (28573507 / 100000000 : ℝ)
  | ⟨26,_⟩ => (286114583 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (35811587 / 125000000 : ℝ)
  | ⟨28,_⟩ => (286869913 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287246233 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287621159 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287995701 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288369361 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288741631 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144556513 / 500000000 : ℝ)
  | ⟨35,_⟩ => (72370887 / 250000000 : ℝ)
  | ⟨36,_⟩ => (144926597 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290221979 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (2905899 / 10000000 : ℝ)
  | ⟨39,_⟩ => (290956447 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58264427 / 200000000 : ℝ)
  | ⟨41,_⟩ => (72921743 / 250000000 : ℝ)
  | ⟨42,_⟩ => (73012739 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12264Cell0 :
    0 ≤ cap12264 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨0,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12264 ⟨0,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨0,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell1 :
    0 ≤ cap12264 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨1,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12264 ⟨1,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨1,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell2 :
    0 ≤ cap12264 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨2,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12264 ⟨2,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨2,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell3 :
    0 ≤ cap12264 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨3,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12264 ⟨3,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨3,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell4 :
    0 ≤ cap12264 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨4,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12264 ⟨4,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨4,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell5 :
    0 ≤ cap12264 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨5,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12264 ⟨5,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨5,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell6 :
    0 ≤ cap12264 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨6,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12264 ⟨6,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨6,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell7 :
    0 ≤ cap12264 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨7,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12264 ⟨7,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨7,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell8 :
    0 ≤ cap12264 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨8,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12264 ⟨8,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨8,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell9 :
    0 ≤ cap12264 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨9,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12264 ⟨9,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨9,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell10 :
    0 ≤ cap12264 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨10,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12264 ⟨10,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨10,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell11 :
    0 ≤ cap12264 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨11,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12264 ⟨11,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨11,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell12 :
    0 ≤ cap12264 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨12,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12264 ⟨12,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨12,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell13 :
    0 ≤ cap12264 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨13,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12264 ⟨13,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨13,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell14 :
    0 ≤ cap12264 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨14,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12264 ⟨14,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨14,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell15 :
    0 ≤ cap12264 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨15,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12264 ⟨15,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨15,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell16 :
    0 ≤ cap12264 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨16,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12264 ⟨16,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨16,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell17 :
    0 ≤ cap12264 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨17,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12264 ⟨17,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨17,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell18 :
    0 ≤ cap12264 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨18,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12264 ⟨18,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨18,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell19 :
    0 ≤ cap12264 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨19,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12264 ⟨19,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨19,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell20 :
    0 ≤ cap12264 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨20,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12264 ⟨20,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨20,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell21 :
    0 ≤ cap12264 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨21,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12264 ⟨21,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨21,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell22 :
    0 ≤ cap12264 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨22,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12264 ⟨22,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨22,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell23 :
    0 ≤ cap12264 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨23,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12264 ⟨23,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨23,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell24 :
    0 ≤ cap12264 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨24,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12264 ⟨24,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨24,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell25 :
    0 ≤ cap12264 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨25,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12264 ⟨25,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨25,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell26 :
    0 ≤ cap12264 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨26,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12264 ⟨26,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨26,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell27 :
    0 ≤ cap12264 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨27,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12264 ⟨27,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨27,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell28 :
    0 ≤ cap12264 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨28,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12264 ⟨28,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨28,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell29 :
    0 ≤ cap12264 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨29,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12264 ⟨29,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨29,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell30 :
    0 ≤ cap12264 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨30,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12264 ⟨30,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨30,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell31 :
    0 ≤ cap12264 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨31,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12264 ⟨31,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨31,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell32 :
    0 ≤ cap12264 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨32,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12264 ⟨32,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨32,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell33 :
    0 ≤ cap12264 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨33,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12264 ⟨33,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨33,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell34 :
    0 ≤ cap12264 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨34,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12264 ⟨34,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨34,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell35 :
    0 ≤ cap12264 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨35,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12264 ⟨35,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨35,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell36 :
    0 ≤ cap12264 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨36,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12264 ⟨36,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨36,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell37 :
    0 ≤ cap12264 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨37,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12264 ⟨37,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨37,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell38 :
    0 ≤ cap12264 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨38,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12264 ⟨38,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨38,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell39 :
    0 ≤ cap12264 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨39,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12264 ⟨39,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨39,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell40 :
    0 ≤ cap12264 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨40,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12264 ⟨40,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨40,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell41 :
    0 ≤ cap12264 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨41,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12264 ⟨41,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨41,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cell42 :
    0 ≤ cap12264 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12264 (parameters ⟨42,by decide⟩)
      (scalarRow12264.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12264 ⟨42,by decide⟩ ∧
    (scalarRow12264.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 ⟨42,by decide⟩ + (scalarRow12264.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12264.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12264.targetFrame := by
  norm_num [cap12264, scalarRow12264, sourceIndex, cell12264, BstLean.Part263.envelope, parameters]

theorem repair12264Cells (j : Fin 43) :
    0 ≤ cap12264 j ∧
    BstLean.Part263.envelope 12264 (parameters j) (scalarRow12264.table (sourceIndex j)).upper ≤ cap12264 j ∧
    (scalarRow12264.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12264 j + (scalarRow12264.table (sourceIndex j)).centre) /
      (scalarRow12264.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12264.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12264Cell0
  | ⟨1,_⟩ => exact repair12264Cell1
  | ⟨2,_⟩ => exact repair12264Cell2
  | ⟨3,_⟩ => exact repair12264Cell3
  | ⟨4,_⟩ => exact repair12264Cell4
  | ⟨5,_⟩ => exact repair12264Cell5
  | ⟨6,_⟩ => exact repair12264Cell6
  | ⟨7,_⟩ => exact repair12264Cell7
  | ⟨8,_⟩ => exact repair12264Cell8
  | ⟨9,_⟩ => exact repair12264Cell9
  | ⟨10,_⟩ => exact repair12264Cell10
  | ⟨11,_⟩ => exact repair12264Cell11
  | ⟨12,_⟩ => exact repair12264Cell12
  | ⟨13,_⟩ => exact repair12264Cell13
  | ⟨14,_⟩ => exact repair12264Cell14
  | ⟨15,_⟩ => exact repair12264Cell15
  | ⟨16,_⟩ => exact repair12264Cell16
  | ⟨17,_⟩ => exact repair12264Cell17
  | ⟨18,_⟩ => exact repair12264Cell18
  | ⟨19,_⟩ => exact repair12264Cell19
  | ⟨20,_⟩ => exact repair12264Cell20
  | ⟨21,_⟩ => exact repair12264Cell21
  | ⟨22,_⟩ => exact repair12264Cell22
  | ⟨23,_⟩ => exact repair12264Cell23
  | ⟨24,_⟩ => exact repair12264Cell24
  | ⟨25,_⟩ => exact repair12264Cell25
  | ⟨26,_⟩ => exact repair12264Cell26
  | ⟨27,_⟩ => exact repair12264Cell27
  | ⟨28,_⟩ => exact repair12264Cell28
  | ⟨29,_⟩ => exact repair12264Cell29
  | ⟨30,_⟩ => exact repair12264Cell30
  | ⟨31,_⟩ => exact repair12264Cell31
  | ⟨32,_⟩ => exact repair12264Cell32
  | ⟨33,_⟩ => exact repair12264Cell33
  | ⟨34,_⟩ => exact repair12264Cell34
  | ⟨35,_⟩ => exact repair12264Cell35
  | ⟨36,_⟩ => exact repair12264Cell36
  | ⟨37,_⟩ => exact repair12264Cell37
  | ⟨38,_⟩ => exact repair12264Cell38
  | ⟨39,_⟩ => exact repair12264Cell39
  | ⟨40,_⟩ => exact repair12264Cell40
  | ⟨41,_⟩ => exact repair12264Cell41
  | ⟨42,_⟩ => exact repair12264Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12264 : FrameRepair 12264 scalarRow12264 where
  cap := cap12264
  cap_nonneg := fun j => (repair12264Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12264])
  endpoint := fun j => (repair12264Cells j).2.1
  endpoint_upper := fun j => (repair12264Cells j).2.2.1
  frame := fun j => (repair12264Cells j).2.2.2

noncomputable def cap12265 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275949699 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276352711 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (34594341 / 125000000 : ℝ)
  | ⟨3,_⟩ => (277155747 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (4336809 / 15625000 : ℝ)
  | ⟨5,_⟩ => (138977407 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278352391 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139374731 / 500000000 : ℝ)
  | ⟨8,_⟩ => (69786389 / 250000000 : ℝ)
  | ⟨9,_⟩ => (139770339 / 500000000 : ℝ)
  | ⟨10,_⟩ => (69983707 / 250000000 : ℝ)
  | ⟨11,_⟩ => (28032753 / 100000000 : ℝ)
  | ⟨12,_⟩ => (140359877 / 500000000 : ℝ)
  | ⟨13,_⟩ => (28111053 / 100000000 : ℝ)
  | ⟨14,_⟩ => (281501239 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (8809089 / 31250000 : ℝ)
  | ⟨16,_⟩ => (141139757 / 500000000 : ℝ)
  | ⟨17,_⟩ => (17666703 / 62500000 : ℝ)
  | ⟨18,_⟩ => (283054043 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (70859977 / 250000000 : ℝ)
  | ⟨20,_⟩ => (283824847 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (71052217 / 250000000 : ℝ)
  | ⟨22,_⟩ => (56918393 / 200000000 : ℝ)
  | ⟨23,_⟩ => (284973651 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (71338731 / 250000000 : ℝ)
  | ⟨25,_⟩ => (71433709 / 250000000 : ℝ)
  | ⟨26,_⟩ => (286114343 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (5729849 / 20000000 : ℝ)
  | ⟨28,_⟩ => (14343483 / 50000000 : ℝ)
  | ⟨29,_⟩ => (143622987 / 500000000 : ℝ)
  | ⟨30,_⟩ => (57524179 / 200000000 : ℝ)
  | ⟨31,_⟩ => (28799543 / 100000000 : ℝ)
  | ⟨32,_⟩ => (57673817 / 200000000 : ℝ)
  | ⟨33,_⟩ => (72185337 / 250000000 : ℝ)
  | ⟨34,_⟩ => (289112737 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289483253 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289852893 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (36277709 / 125000000 : ℝ)
  | ⟨38,_⟩ => (290589587 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (9092379 / 31250000 : ℝ)
  | ⟨40,_⟩ => (29132181 / 100000000 : ℝ)
  | ⟨41,_⟩ => (291686641 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292050619 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12265Cell0 :
    0 ≤ cap12265 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨0,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12265 ⟨0,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨0,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell1 :
    0 ≤ cap12265 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨1,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12265 ⟨1,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨1,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell2 :
    0 ≤ cap12265 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨2,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12265 ⟨2,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨2,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell3 :
    0 ≤ cap12265 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨3,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12265 ⟨3,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨3,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell4 :
    0 ≤ cap12265 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨4,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12265 ⟨4,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨4,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell5 :
    0 ≤ cap12265 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨5,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12265 ⟨5,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨5,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell6 :
    0 ≤ cap12265 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨6,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12265 ⟨6,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨6,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell7 :
    0 ≤ cap12265 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨7,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12265 ⟨7,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨7,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell8 :
    0 ≤ cap12265 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨8,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12265 ⟨8,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨8,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell9 :
    0 ≤ cap12265 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨9,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12265 ⟨9,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨9,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell10 :
    0 ≤ cap12265 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨10,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12265 ⟨10,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨10,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell11 :
    0 ≤ cap12265 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨11,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12265 ⟨11,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨11,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell12 :
    0 ≤ cap12265 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨12,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12265 ⟨12,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨12,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell13 :
    0 ≤ cap12265 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨13,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12265 ⟨13,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨13,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell14 :
    0 ≤ cap12265 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨14,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12265 ⟨14,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨14,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell15 :
    0 ≤ cap12265 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨15,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12265 ⟨15,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨15,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell16 :
    0 ≤ cap12265 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨16,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12265 ⟨16,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨16,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell17 :
    0 ≤ cap12265 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨17,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12265 ⟨17,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨17,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell18 :
    0 ≤ cap12265 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨18,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12265 ⟨18,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨18,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell19 :
    0 ≤ cap12265 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨19,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12265 ⟨19,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨19,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell20 :
    0 ≤ cap12265 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨20,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12265 ⟨20,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨20,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell21 :
    0 ≤ cap12265 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨21,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12265 ⟨21,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨21,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell22 :
    0 ≤ cap12265 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨22,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12265 ⟨22,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨22,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell23 :
    0 ≤ cap12265 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨23,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12265 ⟨23,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨23,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell24 :
    0 ≤ cap12265 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨24,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12265 ⟨24,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨24,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell25 :
    0 ≤ cap12265 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨25,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12265 ⟨25,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨25,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell26 :
    0 ≤ cap12265 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨26,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12265 ⟨26,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨26,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell27 :
    0 ≤ cap12265 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨27,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12265 ⟨27,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨27,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell28 :
    0 ≤ cap12265 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨28,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12265 ⟨28,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨28,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell29 :
    0 ≤ cap12265 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨29,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12265 ⟨29,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨29,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell30 :
    0 ≤ cap12265 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨30,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12265 ⟨30,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨30,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell31 :
    0 ≤ cap12265 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨31,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12265 ⟨31,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨31,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell32 :
    0 ≤ cap12265 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨32,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12265 ⟨32,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨32,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell33 :
    0 ≤ cap12265 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨33,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12265 ⟨33,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨33,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell34 :
    0 ≤ cap12265 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨34,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12265 ⟨34,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨34,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell35 :
    0 ≤ cap12265 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨35,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12265 ⟨35,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨35,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell36 :
    0 ≤ cap12265 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨36,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12265 ⟨36,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨36,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell37 :
    0 ≤ cap12265 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨37,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12265 ⟨37,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨37,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell38 :
    0 ≤ cap12265 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨38,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12265 ⟨38,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨38,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell39 :
    0 ≤ cap12265 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨39,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12265 ⟨39,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨39,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell40 :
    0 ≤ cap12265 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨40,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12265 ⟨40,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨40,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell41 :
    0 ≤ cap12265 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨41,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12265 ⟨41,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨41,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cell42 :
    0 ≤ cap12265 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12265 (parameters ⟨42,by decide⟩)
      (scalarRow12265.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12265 ⟨42,by decide⟩ ∧
    (scalarRow12265.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 ⟨42,by decide⟩ + (scalarRow12265.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12265.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12265.targetFrame := by
  norm_num [cap12265, scalarRow12265, sourceIndex, cell12265, BstLean.Part263.envelope, parameters]

theorem repair12265Cells (j : Fin 43) :
    0 ≤ cap12265 j ∧
    BstLean.Part263.envelope 12265 (parameters j) (scalarRow12265.table (sourceIndex j)).upper ≤ cap12265 j ∧
    (scalarRow12265.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12265 j + (scalarRow12265.table (sourceIndex j)).centre) /
      (scalarRow12265.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12265.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12265Cell0
  | ⟨1,_⟩ => exact repair12265Cell1
  | ⟨2,_⟩ => exact repair12265Cell2
  | ⟨3,_⟩ => exact repair12265Cell3
  | ⟨4,_⟩ => exact repair12265Cell4
  | ⟨5,_⟩ => exact repair12265Cell5
  | ⟨6,_⟩ => exact repair12265Cell6
  | ⟨7,_⟩ => exact repair12265Cell7
  | ⟨8,_⟩ => exact repair12265Cell8
  | ⟨9,_⟩ => exact repair12265Cell9
  | ⟨10,_⟩ => exact repair12265Cell10
  | ⟨11,_⟩ => exact repair12265Cell11
  | ⟨12,_⟩ => exact repair12265Cell12
  | ⟨13,_⟩ => exact repair12265Cell13
  | ⟨14,_⟩ => exact repair12265Cell14
  | ⟨15,_⟩ => exact repair12265Cell15
  | ⟨16,_⟩ => exact repair12265Cell16
  | ⟨17,_⟩ => exact repair12265Cell17
  | ⟨18,_⟩ => exact repair12265Cell18
  | ⟨19,_⟩ => exact repair12265Cell19
  | ⟨20,_⟩ => exact repair12265Cell20
  | ⟨21,_⟩ => exact repair12265Cell21
  | ⟨22,_⟩ => exact repair12265Cell22
  | ⟨23,_⟩ => exact repair12265Cell23
  | ⟨24,_⟩ => exact repair12265Cell24
  | ⟨25,_⟩ => exact repair12265Cell25
  | ⟨26,_⟩ => exact repair12265Cell26
  | ⟨27,_⟩ => exact repair12265Cell27
  | ⟨28,_⟩ => exact repair12265Cell28
  | ⟨29,_⟩ => exact repair12265Cell29
  | ⟨30,_⟩ => exact repair12265Cell30
  | ⟨31,_⟩ => exact repair12265Cell31
  | ⟨32,_⟩ => exact repair12265Cell32
  | ⟨33,_⟩ => exact repair12265Cell33
  | ⟨34,_⟩ => exact repair12265Cell34
  | ⟨35,_⟩ => exact repair12265Cell35
  | ⟨36,_⟩ => exact repair12265Cell36
  | ⟨37,_⟩ => exact repair12265Cell37
  | ⟨38,_⟩ => exact repair12265Cell38
  | ⟨39,_⟩ => exact repair12265Cell39
  | ⟨40,_⟩ => exact repair12265Cell40
  | ⟨41,_⟩ => exact repair12265Cell41
  | ⟨42,_⟩ => exact repair12265Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12265 : FrameRepair 12265 scalarRow12265 where
  cap := cap12265
  cap_nonneg := fun j => (repair12265Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12265])
  endpoint := fun j => (repair12265Cells j).2.1
  endpoint_upper := fun j => (repair12265Cells j).2.2.1
  frame := fun j => (repair12265Cells j).2.2.2

noncomputable def cap12266 : Fin 43 → ℝ
  | ⟨0,_⟩ => (34493703 / 125000000 : ℝ)
  | ⟨1,_⟩ => (276352629 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (3459433 / 12500000 : ℝ)
  | ⟨3,_⟩ => (69288913 / 250000000 : ℝ)
  | ⟨4,_⟩ => (138777837 / 500000000 : ℝ)
  | ⟨5,_⟩ => (138977353 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278352277 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (278749341 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279145429 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (4367821 / 15625000 : ℝ)
  | ⟨10,_⟩ => (8747959 / 31250000 : ℝ)
  | ⟨11,_⟩ => (35040923 / 125000000 : ℝ)
  | ⟨12,_⟩ => (280719601 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281110371 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140750537 / 500000000 : ℝ)
  | ⟨15,_⟩ => (70472669 / 250000000 : ℝ)
  | ⟨16,_⟩ => (35284917 / 125000000 : ℝ)
  | ⟨17,_⟩ => (35333383 / 125000000 : ℝ)
  | ⟨18,_⟩ => (70763463 / 250000000 : ℝ)
  | ⟨19,_⟩ => (8857491 / 31250000 : ℝ)
  | ⟨20,_⟩ => (70956161 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284208659 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (1138367 / 4000000 : ℝ)
  | ⟨23,_⟩ => (28497343 / 100000000 : ℝ)
  | ⟨24,_⟩ => (35669337 / 125000000 : ℝ)
  | ⟨25,_⟩ => (142867301 / 500000000 : ℝ)
  | ⟨26,_⟩ => (286114103 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (286492203 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (8964669 / 31250000 : ℝ)
  | ⟨29,_⟩ => (71811429 / 250000000 : ℝ)
  | ⟨30,_⟩ => (28762063 / 100000000 : ℝ)
  | ⟨31,_⟩ => (287995159 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (36046101 / 125000000 : ℝ)
  | ⟨33,_⟩ => (144370533 / 500000000 : ℝ)
  | ⟨34,_⟩ => (2258691 / 7812500 : ℝ)
  | ⟨35,_⟩ => (144741479 / 500000000 : ℝ)
  | ⟨36,_⟩ => (18115787 / 62500000 : ℝ)
  | ⟨37,_⟩ => (58044273 / 200000000 : ℝ)
  | ⟨38,_⟩ => (290589273 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290955809 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58264297 / 200000000 : ℝ)
  | ⟨41,_⟩ => (29168631 / 100000000 : ℝ)
  | ⟨42,_⟩ => (146025141 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12266Cell0 :
    0 ≤ cap12266 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨0,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12266 ⟨0,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨0,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell1 :
    0 ≤ cap12266 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨1,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12266 ⟨1,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨1,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell2 :
    0 ≤ cap12266 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨2,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12266 ⟨2,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨2,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell3 :
    0 ≤ cap12266 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨3,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12266 ⟨3,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨3,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell4 :
    0 ≤ cap12266 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨4,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12266 ⟨4,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨4,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell5 :
    0 ≤ cap12266 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨5,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12266 ⟨5,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨5,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell6 :
    0 ≤ cap12266 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨6,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12266 ⟨6,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨6,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell7 :
    0 ≤ cap12266 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨7,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12266 ⟨7,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨7,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell8 :
    0 ≤ cap12266 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨8,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12266 ⟨8,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨8,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell9 :
    0 ≤ cap12266 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨9,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12266 ⟨9,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨9,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell10 :
    0 ≤ cap12266 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨10,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12266 ⟨10,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨10,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell11 :
    0 ≤ cap12266 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨11,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12266 ⟨11,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨11,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell12 :
    0 ≤ cap12266 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨12,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12266 ⟨12,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨12,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell13 :
    0 ≤ cap12266 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨13,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12266 ⟨13,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨13,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell14 :
    0 ≤ cap12266 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨14,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12266 ⟨14,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨14,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell15 :
    0 ≤ cap12266 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨15,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12266 ⟨15,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨15,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell16 :
    0 ≤ cap12266 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨16,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12266 ⟨16,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨16,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell17 :
    0 ≤ cap12266 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨17,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12266 ⟨17,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨17,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell18 :
    0 ≤ cap12266 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨18,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12266 ⟨18,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨18,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell19 :
    0 ≤ cap12266 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨19,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12266 ⟨19,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨19,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell20 :
    0 ≤ cap12266 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨20,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12266 ⟨20,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨20,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell21 :
    0 ≤ cap12266 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨21,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12266 ⟨21,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨21,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell22 :
    0 ≤ cap12266 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨22,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12266 ⟨22,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨22,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell23 :
    0 ≤ cap12266 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨23,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12266 ⟨23,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨23,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell24 :
    0 ≤ cap12266 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨24,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12266 ⟨24,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨24,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell25 :
    0 ≤ cap12266 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨25,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12266 ⟨25,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨25,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell26 :
    0 ≤ cap12266 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨26,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12266 ⟨26,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨26,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell27 :
    0 ≤ cap12266 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨27,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12266 ⟨27,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨27,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell28 :
    0 ≤ cap12266 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨28,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12266 ⟨28,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨28,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell29 :
    0 ≤ cap12266 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨29,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12266 ⟨29,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨29,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell30 :
    0 ≤ cap12266 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨30,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12266 ⟨30,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨30,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell31 :
    0 ≤ cap12266 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨31,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12266 ⟨31,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨31,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell32 :
    0 ≤ cap12266 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨32,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12266 ⟨32,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨32,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell33 :
    0 ≤ cap12266 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨33,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12266 ⟨33,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨33,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell34 :
    0 ≤ cap12266 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨34,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12266 ⟨34,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨34,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell35 :
    0 ≤ cap12266 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨35,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12266 ⟨35,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨35,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell36 :
    0 ≤ cap12266 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨36,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12266 ⟨36,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨36,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell37 :
    0 ≤ cap12266 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨37,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12266 ⟨37,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨37,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell38 :
    0 ≤ cap12266 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨38,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12266 ⟨38,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨38,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell39 :
    0 ≤ cap12266 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨39,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12266 ⟨39,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨39,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell40 :
    0 ≤ cap12266 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨40,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12266 ⟨40,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨40,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell41 :
    0 ≤ cap12266 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨41,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12266 ⟨41,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨41,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cell42 :
    0 ≤ cap12266 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12266 (parameters ⟨42,by decide⟩)
      (scalarRow12266.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12266 ⟨42,by decide⟩ ∧
    (scalarRow12266.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 ⟨42,by decide⟩ + (scalarRow12266.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12266.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12266.targetFrame := by
  norm_num [cap12266, scalarRow12266, sourceIndex, cell12266, BstLean.Part263.envelope, parameters]

theorem repair12266Cells (j : Fin 43) :
    0 ≤ cap12266 j ∧
    BstLean.Part263.envelope 12266 (parameters j) (scalarRow12266.table (sourceIndex j)).upper ≤ cap12266 j ∧
    (scalarRow12266.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12266 j + (scalarRow12266.table (sourceIndex j)).centre) /
      (scalarRow12266.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12266.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12266Cell0
  | ⟨1,_⟩ => exact repair12266Cell1
  | ⟨2,_⟩ => exact repair12266Cell2
  | ⟨3,_⟩ => exact repair12266Cell3
  | ⟨4,_⟩ => exact repair12266Cell4
  | ⟨5,_⟩ => exact repair12266Cell5
  | ⟨6,_⟩ => exact repair12266Cell6
  | ⟨7,_⟩ => exact repair12266Cell7
  | ⟨8,_⟩ => exact repair12266Cell8
  | ⟨9,_⟩ => exact repair12266Cell9
  | ⟨10,_⟩ => exact repair12266Cell10
  | ⟨11,_⟩ => exact repair12266Cell11
  | ⟨12,_⟩ => exact repair12266Cell12
  | ⟨13,_⟩ => exact repair12266Cell13
  | ⟨14,_⟩ => exact repair12266Cell14
  | ⟨15,_⟩ => exact repair12266Cell15
  | ⟨16,_⟩ => exact repair12266Cell16
  | ⟨17,_⟩ => exact repair12266Cell17
  | ⟨18,_⟩ => exact repair12266Cell18
  | ⟨19,_⟩ => exact repair12266Cell19
  | ⟨20,_⟩ => exact repair12266Cell20
  | ⟨21,_⟩ => exact repair12266Cell21
  | ⟨22,_⟩ => exact repair12266Cell22
  | ⟨23,_⟩ => exact repair12266Cell23
  | ⟨24,_⟩ => exact repair12266Cell24
  | ⟨25,_⟩ => exact repair12266Cell25
  | ⟨26,_⟩ => exact repair12266Cell26
  | ⟨27,_⟩ => exact repair12266Cell27
  | ⟨28,_⟩ => exact repair12266Cell28
  | ⟨29,_⟩ => exact repair12266Cell29
  | ⟨30,_⟩ => exact repair12266Cell30
  | ⟨31,_⟩ => exact repair12266Cell31
  | ⟨32,_⟩ => exact repair12266Cell32
  | ⟨33,_⟩ => exact repair12266Cell33
  | ⟨34,_⟩ => exact repair12266Cell34
  | ⟨35,_⟩ => exact repair12266Cell35
  | ⟨36,_⟩ => exact repair12266Cell36
  | ⟨37,_⟩ => exact repair12266Cell37
  | ⟨38,_⟩ => exact repair12266Cell38
  | ⟨39,_⟩ => exact repair12266Cell39
  | ⟨40,_⟩ => exact repair12266Cell40
  | ⟨41,_⟩ => exact repair12266Cell41
  | ⟨42,_⟩ => exact repair12266Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12266 : FrameRepair 12266 scalarRow12266 where
  cap := cap12266
  cap_nonneg := fun j => (repair12266Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12266])
  endpoint := fun j => (repair12266Cells j).2.1
  endpoint_upper := fun j => (repair12266Cells j).2.2.1
  frame := fun j => (repair12266Cells j).2.2.2

noncomputable def cap12267 : Fin 43 → ℝ
  | ⟨0,_⟩ => (68987387 / 250000000 : ℝ)
  | ⟨1,_⟩ => (276352547 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276754551 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277155557 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277555573 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138977299 / 500000000 : ℝ)
  | ⟨6,_⟩ => (139176081 / 500000000 : ℝ)
  | ⟨7,_⟩ => (13937461 / 50000000 : ℝ)
  | ⟨8,_⟩ => (139572651 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279540411 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (69983637 / 250000000 : ℝ)
  | ⟨11,_⟩ => (280327237 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (35089931 / 125000000 : ℝ)
  | ⟨13,_⟩ => (70277553 / 250000000 : ℝ)
  | ⟨14,_⟩ => (281500909 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (56378101 / 200000000 : ℝ)
  | ⟨16,_⟩ => (141139579 / 500000000 : ℝ)
  | ⟨17,_⟩ => (441667 / 1562500 : ℝ)
  | ⟨18,_⟩ => (141526831 / 500000000 : ℝ)
  | ⟨19,_⟩ => (56687903 / 200000000 : ℝ)
  | ⟨20,_⟩ => (283824441 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (5684169 / 20000000 : ℝ)
  | ⟨22,_⟩ => (142295767 / 500000000 : ℝ)
  | ⟨23,_⟩ => (35621651 / 125000000 : ℝ)
  | ⟨24,_⟩ => (285354469 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (8929199 / 31250000 : ℝ)
  | ⟨26,_⟩ => (143056931 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286491957 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (57373831 / 200000000 : ℝ)
  | ⟨29,_⟩ => (287245457 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (57524073 / 200000000 : ℝ)
  | ⟨31,_⟩ => (287994889 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288368531 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288740783 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289112159 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289482663 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289852291 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (145110529 / 500000000 : ℝ)
  | ⟨38,_⟩ => (1816181 / 6250000 : ℝ)
  | ⟨39,_⟩ => (29095549 / 100000000 : ℝ)
  | ⟨40,_⟩ => (7283029 / 25000000 : ℝ)
  | ⟨41,_⟩ => (291685979 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (58409989 / 200000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12267Cell0 :
    0 ≤ cap12267 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨0,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12267 ⟨0,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨0,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell1 :
    0 ≤ cap12267 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨1,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12267 ⟨1,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨1,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell2 :
    0 ≤ cap12267 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨2,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12267 ⟨2,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨2,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell3 :
    0 ≤ cap12267 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨3,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12267 ⟨3,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨3,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell4 :
    0 ≤ cap12267 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨4,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12267 ⟨4,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨4,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell5 :
    0 ≤ cap12267 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨5,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12267 ⟨5,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨5,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell6 :
    0 ≤ cap12267 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨6,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12267 ⟨6,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨6,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell7 :
    0 ≤ cap12267 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨7,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12267 ⟨7,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨7,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell8 :
    0 ≤ cap12267 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨8,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12267 ⟨8,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨8,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell9 :
    0 ≤ cap12267 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨9,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12267 ⟨9,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨9,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell10 :
    0 ≤ cap12267 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨10,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12267 ⟨10,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨10,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell11 :
    0 ≤ cap12267 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨11,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12267 ⟨11,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨11,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell12 :
    0 ≤ cap12267 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨12,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12267 ⟨12,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨12,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell13 :
    0 ≤ cap12267 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨13,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12267 ⟨13,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨13,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell14 :
    0 ≤ cap12267 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨14,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12267 ⟨14,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨14,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell15 :
    0 ≤ cap12267 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨15,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12267 ⟨15,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨15,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell16 :
    0 ≤ cap12267 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨16,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12267 ⟨16,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨16,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell17 :
    0 ≤ cap12267 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨17,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12267 ⟨17,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨17,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell18 :
    0 ≤ cap12267 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨18,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12267 ⟨18,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨18,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell19 :
    0 ≤ cap12267 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨19,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12267 ⟨19,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨19,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell20 :
    0 ≤ cap12267 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨20,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12267 ⟨20,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨20,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell21 :
    0 ≤ cap12267 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨21,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12267 ⟨21,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨21,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell22 :
    0 ≤ cap12267 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨22,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12267 ⟨22,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨22,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell23 :
    0 ≤ cap12267 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨23,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12267 ⟨23,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨23,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell24 :
    0 ≤ cap12267 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨24,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12267 ⟨24,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨24,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell25 :
    0 ≤ cap12267 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨25,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12267 ⟨25,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨25,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell26 :
    0 ≤ cap12267 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨26,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12267 ⟨26,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨26,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell27 :
    0 ≤ cap12267 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨27,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12267 ⟨27,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨27,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell28 :
    0 ≤ cap12267 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨28,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12267 ⟨28,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨28,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell29 :
    0 ≤ cap12267 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨29,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12267 ⟨29,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨29,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell30 :
    0 ≤ cap12267 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨30,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12267 ⟨30,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨30,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell31 :
    0 ≤ cap12267 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨31,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12267 ⟨31,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨31,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell32 :
    0 ≤ cap12267 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨32,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12267 ⟨32,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨32,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell33 :
    0 ≤ cap12267 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨33,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12267 ⟨33,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨33,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell34 :
    0 ≤ cap12267 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨34,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12267 ⟨34,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨34,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell35 :
    0 ≤ cap12267 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨35,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12267 ⟨35,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨35,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell36 :
    0 ≤ cap12267 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨36,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12267 ⟨36,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨36,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell37 :
    0 ≤ cap12267 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨37,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12267 ⟨37,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨37,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell38 :
    0 ≤ cap12267 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨38,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12267 ⟨38,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨38,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell39 :
    0 ≤ cap12267 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨39,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12267 ⟨39,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨39,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell40 :
    0 ≤ cap12267 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨40,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12267 ⟨40,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨40,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell41 :
    0 ≤ cap12267 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨41,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12267 ⟨41,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨41,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cell42 :
    0 ≤ cap12267 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12267 (parameters ⟨42,by decide⟩)
      (scalarRow12267.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12267 ⟨42,by decide⟩ ∧
    (scalarRow12267.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 ⟨42,by decide⟩ + (scalarRow12267.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12267.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12267.targetFrame := by
  norm_num [cap12267, scalarRow12267, sourceIndex, cell12267, BstLean.Part263.envelope, parameters]

theorem repair12267Cells (j : Fin 43) :
    0 ≤ cap12267 j ∧
    BstLean.Part263.envelope 12267 (parameters j) (scalarRow12267.table (sourceIndex j)).upper ≤ cap12267 j ∧
    (scalarRow12267.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12267 j + (scalarRow12267.table (sourceIndex j)).centre) /
      (scalarRow12267.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12267.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12267Cell0
  | ⟨1,_⟩ => exact repair12267Cell1
  | ⟨2,_⟩ => exact repair12267Cell2
  | ⟨3,_⟩ => exact repair12267Cell3
  | ⟨4,_⟩ => exact repair12267Cell4
  | ⟨5,_⟩ => exact repair12267Cell5
  | ⟨6,_⟩ => exact repair12267Cell6
  | ⟨7,_⟩ => exact repair12267Cell7
  | ⟨8,_⟩ => exact repair12267Cell8
  | ⟨9,_⟩ => exact repair12267Cell9
  | ⟨10,_⟩ => exact repair12267Cell10
  | ⟨11,_⟩ => exact repair12267Cell11
  | ⟨12,_⟩ => exact repair12267Cell12
  | ⟨13,_⟩ => exact repair12267Cell13
  | ⟨14,_⟩ => exact repair12267Cell14
  | ⟨15,_⟩ => exact repair12267Cell15
  | ⟨16,_⟩ => exact repair12267Cell16
  | ⟨17,_⟩ => exact repair12267Cell17
  | ⟨18,_⟩ => exact repair12267Cell18
  | ⟨19,_⟩ => exact repair12267Cell19
  | ⟨20,_⟩ => exact repair12267Cell20
  | ⟨21,_⟩ => exact repair12267Cell21
  | ⟨22,_⟩ => exact repair12267Cell22
  | ⟨23,_⟩ => exact repair12267Cell23
  | ⟨24,_⟩ => exact repair12267Cell24
  | ⟨25,_⟩ => exact repair12267Cell25
  | ⟨26,_⟩ => exact repair12267Cell26
  | ⟨27,_⟩ => exact repair12267Cell27
  | ⟨28,_⟩ => exact repair12267Cell28
  | ⟨29,_⟩ => exact repair12267Cell29
  | ⟨30,_⟩ => exact repair12267Cell30
  | ⟨31,_⟩ => exact repair12267Cell31
  | ⟨32,_⟩ => exact repair12267Cell32
  | ⟨33,_⟩ => exact repair12267Cell33
  | ⟨34,_⟩ => exact repair12267Cell34
  | ⟨35,_⟩ => exact repair12267Cell35
  | ⟨36,_⟩ => exact repair12267Cell36
  | ⟨37,_⟩ => exact repair12267Cell37
  | ⟨38,_⟩ => exact repair12267Cell38
  | ⟨39,_⟩ => exact repair12267Cell39
  | ⟨40,_⟩ => exact repair12267Cell40
  | ⟨41,_⟩ => exact repair12267Cell41
  | ⟨42,_⟩ => exact repair12267Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12267 : FrameRepair 12267 scalarRow12267 where
  cap := cap12267
  cap_nonneg := fun j => (repair12267Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12267])
  endpoint := fun j => (repair12267Cells j).2.1
  endpoint_upper := fun j => (repair12267Cells j).2.2.1
  frame := fun j => (repair12267Cells j).2.2.2

noncomputable def cap12268 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275949473 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (55270493 / 200000000 : ℝ)
  | ⟨2,_⟩ => (138377231 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138577731 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277555471 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (27795449 / 100000000 : ℝ)
  | ⟨6,_⟩ => (17397003 / 62500000 : ℝ)
  | ⟨7,_⟩ => (278749099 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (139572587 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279540277 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (34991801 / 125000000 : ℝ)
  | ⟨11,_⟩ => (280327091 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (4386239 / 15625000 : ℝ)
  | ⟨13,_⟩ => (281110053 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281500743 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (281890333 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (14113949 / 50000000 : ℝ)
  | ⟨17,_⟩ => (35333337 / 125000000 : ℝ)
  | ⟨18,_⟩ => (283053471 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141719659 / 500000000 : ℝ)
  | ⟨20,_⟩ => (141912119 / 500000000 : ℝ)
  | ⟨21,_⟩ => (3552603 / 12500000 : ℝ)
  | ⟨22,_⟩ => (284591319 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142486493 / 500000000 : ℝ)
  | ⟨24,_⟩ => (285354241 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (142867067 / 500000000 : ℝ)
  | ⟨26,_⟩ => (143056811 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286491711 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286868903 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287245199 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287620101 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143997309 / 500000000 : ℝ)
  | ⟨32,_⟩ => (144184127 / 500000000 : ℝ)
  | ⟨33,_⟩ => (577481 / 2000000 : ℝ)
  | ⟨34,_⟩ => (28911187 / 100000000 : ℝ)
  | ⟨35,_⟩ => (2261581 / 7812500 : ℝ)
  | ⟨36,_⟩ => (28985199 / 100000000 : ℝ)
  | ⟨37,_⟩ => (290220751 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290588647 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290955171 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58264167 / 200000000 : ℝ)
  | ⟨41,_⟩ => (18230353 / 62500000 : ℝ)
  | ⟨42,_⟩ => (36506201 / 125000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12268Cell0 :
    0 ≤ cap12268 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨0,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12268 ⟨0,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨0,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell1 :
    0 ≤ cap12268 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨1,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12268 ⟨1,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨1,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell2 :
    0 ≤ cap12268 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨2,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12268 ⟨2,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨2,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell3 :
    0 ≤ cap12268 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨3,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12268 ⟨3,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨3,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell4 :
    0 ≤ cap12268 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨4,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12268 ⟨4,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨4,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell5 :
    0 ≤ cap12268 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨5,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12268 ⟨5,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨5,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell6 :
    0 ≤ cap12268 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨6,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12268 ⟨6,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨6,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell7 :
    0 ≤ cap12268 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨7,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12268 ⟨7,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨7,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell8 :
    0 ≤ cap12268 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨8,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12268 ⟨8,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨8,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell9 :
    0 ≤ cap12268 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨9,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12268 ⟨9,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨9,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell10 :
    0 ≤ cap12268 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨10,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12268 ⟨10,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨10,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell11 :
    0 ≤ cap12268 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨11,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12268 ⟨11,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨11,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell12 :
    0 ≤ cap12268 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨12,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12268 ⟨12,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨12,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell13 :
    0 ≤ cap12268 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨13,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12268 ⟨13,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨13,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell14 :
    0 ≤ cap12268 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨14,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12268 ⟨14,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨14,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell15 :
    0 ≤ cap12268 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨15,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12268 ⟨15,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨15,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell16 :
    0 ≤ cap12268 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨16,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12268 ⟨16,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨16,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell17 :
    0 ≤ cap12268 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨17,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12268 ⟨17,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨17,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell18 :
    0 ≤ cap12268 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨18,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12268 ⟨18,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨18,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell19 :
    0 ≤ cap12268 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨19,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12268 ⟨19,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨19,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell20 :
    0 ≤ cap12268 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨20,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12268 ⟨20,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨20,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell21 :
    0 ≤ cap12268 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨21,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12268 ⟨21,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨21,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell22 :
    0 ≤ cap12268 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨22,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12268 ⟨22,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨22,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell23 :
    0 ≤ cap12268 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨23,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12268 ⟨23,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨23,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell24 :
    0 ≤ cap12268 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨24,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12268 ⟨24,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨24,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell25 :
    0 ≤ cap12268 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨25,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12268 ⟨25,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨25,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell26 :
    0 ≤ cap12268 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨26,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12268 ⟨26,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨26,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell27 :
    0 ≤ cap12268 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨27,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12268 ⟨27,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨27,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell28 :
    0 ≤ cap12268 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨28,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12268 ⟨28,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨28,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell29 :
    0 ≤ cap12268 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨29,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12268 ⟨29,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨29,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell30 :
    0 ≤ cap12268 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨30,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12268 ⟨30,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨30,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell31 :
    0 ≤ cap12268 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨31,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12268 ⟨31,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨31,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell32 :
    0 ≤ cap12268 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨32,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12268 ⟨32,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨32,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell33 :
    0 ≤ cap12268 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨33,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12268 ⟨33,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨33,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell34 :
    0 ≤ cap12268 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨34,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12268 ⟨34,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨34,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell35 :
    0 ≤ cap12268 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨35,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12268 ⟨35,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨35,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell36 :
    0 ≤ cap12268 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨36,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12268 ⟨36,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨36,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell37 :
    0 ≤ cap12268 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨37,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12268 ⟨37,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨37,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell38 :
    0 ≤ cap12268 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨38,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12268 ⟨38,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨38,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell39 :
    0 ≤ cap12268 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨39,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12268 ⟨39,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨39,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell40 :
    0 ≤ cap12268 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨40,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12268 ⟨40,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨40,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell41 :
    0 ≤ cap12268 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨41,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12268 ⟨41,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨41,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cell42 :
    0 ≤ cap12268 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12268 (parameters ⟨42,by decide⟩)
      (scalarRow12268.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12268 ⟨42,by decide⟩ ∧
    (scalarRow12268.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 ⟨42,by decide⟩ + (scalarRow12268.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12268.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12268.targetFrame := by
  norm_num [cap12268, scalarRow12268, sourceIndex, cell12268, BstLean.Part263.envelope, parameters]

theorem repair12268Cells (j : Fin 43) :
    0 ≤ cap12268 j ∧
    BstLean.Part263.envelope 12268 (parameters j) (scalarRow12268.table (sourceIndex j)).upper ≤ cap12268 j ∧
    (scalarRow12268.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12268 j + (scalarRow12268.table (sourceIndex j)).centre) /
      (scalarRow12268.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12268.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12268Cell0
  | ⟨1,_⟩ => exact repair12268Cell1
  | ⟨2,_⟩ => exact repair12268Cell2
  | ⟨3,_⟩ => exact repair12268Cell3
  | ⟨4,_⟩ => exact repair12268Cell4
  | ⟨5,_⟩ => exact repair12268Cell5
  | ⟨6,_⟩ => exact repair12268Cell6
  | ⟨7,_⟩ => exact repair12268Cell7
  | ⟨8,_⟩ => exact repair12268Cell8
  | ⟨9,_⟩ => exact repair12268Cell9
  | ⟨10,_⟩ => exact repair12268Cell10
  | ⟨11,_⟩ => exact repair12268Cell11
  | ⟨12,_⟩ => exact repair12268Cell12
  | ⟨13,_⟩ => exact repair12268Cell13
  | ⟨14,_⟩ => exact repair12268Cell14
  | ⟨15,_⟩ => exact repair12268Cell15
  | ⟨16,_⟩ => exact repair12268Cell16
  | ⟨17,_⟩ => exact repair12268Cell17
  | ⟨18,_⟩ => exact repair12268Cell18
  | ⟨19,_⟩ => exact repair12268Cell19
  | ⟨20,_⟩ => exact repair12268Cell20
  | ⟨21,_⟩ => exact repair12268Cell21
  | ⟨22,_⟩ => exact repair12268Cell22
  | ⟨23,_⟩ => exact repair12268Cell23
  | ⟨24,_⟩ => exact repair12268Cell24
  | ⟨25,_⟩ => exact repair12268Cell25
  | ⟨26,_⟩ => exact repair12268Cell26
  | ⟨27,_⟩ => exact repair12268Cell27
  | ⟨28,_⟩ => exact repair12268Cell28
  | ⟨29,_⟩ => exact repair12268Cell29
  | ⟨30,_⟩ => exact repair12268Cell30
  | ⟨31,_⟩ => exact repair12268Cell31
  | ⟨32,_⟩ => exact repair12268Cell32
  | ⟨33,_⟩ => exact repair12268Cell33
  | ⟨34,_⟩ => exact repair12268Cell34
  | ⟨35,_⟩ => exact repair12268Cell35
  | ⟨36,_⟩ => exact repair12268Cell36
  | ⟨37,_⟩ => exact repair12268Cell37
  | ⟨38,_⟩ => exact repair12268Cell38
  | ⟨39,_⟩ => exact repair12268Cell39
  | ⟨40,_⟩ => exact repair12268Cell40
  | ⟨41,_⟩ => exact repair12268Cell41
  | ⟨42,_⟩ => exact repair12268Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12268 : FrameRepair 12268 scalarRow12268 where
  cap := cap12268
  cap_nonneg := fun j => (repair12268Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12268])
  endpoint := fun j => (repair12268Cells j).2.1
  endpoint_upper := fun j => (repair12268Cells j).2.2.1
  frame := fun j => (repair12268Cells j).2.2.2

noncomputable def cap12269 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275949397 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276352383 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138377187 / 500000000 : ℝ)
  | ⟨3,_⟩ => (277155367 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (27755537 / 100000000 : ℝ)
  | ⟨5,_⟩ => (138977191 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278351933 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139374489 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279145047 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279540143 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (69983567 / 250000000 : ℝ)
  | ⟨11,_⟩ => (56065389 / 200000000 : ℝ)
  | ⟨12,_⟩ => (280719143 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140554947 / 500000000 : ℝ)
  | ⟨14,_⟩ => (140750289 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140945081 / 500000000 : ℝ)
  | ⟨16,_⟩ => (141139401 / 500000000 : ℝ)
  | ⟨17,_⟩ => (282666511 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283053281 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141719561 / 500000000 : ℝ)
  | ⟨20,_⟩ => (56764807 / 200000000 : ℝ)
  | ⟨21,_⟩ => (284208031 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (555842 / 1953125 : ℝ)
  | ⟨23,_⟩ => (56994553 / 200000000 : ℝ)
  | ⟨24,_⟩ => (285354013 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (2857339 / 10000000 : ℝ)
  | ⟨26,_⟩ => (143056691 / 500000000 : ℝ)
  | ⟨27,_⟩ => (57298293 / 200000000 : ℝ)
  | ⟨28,_⟩ => (286868651 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (14362247 / 50000000 : ℝ)
  | ⟨30,_⟩ => (71904959 / 250000000 : ℝ)
  | ⟨31,_⟩ => (287994347 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288367977 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (288740217 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (289111581 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289482073 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289851689 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (72555111 / 250000000 : ℝ)
  | ⟨38,_⟩ => (58117667 / 200000000 : ℝ)
  | ⟨39,_⟩ => (72738713 / 250000000 : ℝ)
  | ⟨40,_⟩ => (29132051 / 100000000 : ℝ)
  | ⟨41,_⟩ => (291685317 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (292049271 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12269Cell0 :
    0 ≤ cap12269 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨0,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12269 ⟨0,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨0,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell1 :
    0 ≤ cap12269 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨1,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12269 ⟨1,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨1,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell2 :
    0 ≤ cap12269 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨2,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12269 ⟨2,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨2,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell3 :
    0 ≤ cap12269 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨3,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12269 ⟨3,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨3,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell4 :
    0 ≤ cap12269 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨4,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12269 ⟨4,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨4,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell5 :
    0 ≤ cap12269 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨5,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12269 ⟨5,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨5,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell6 :
    0 ≤ cap12269 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨6,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12269 ⟨6,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨6,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell7 :
    0 ≤ cap12269 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨7,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12269 ⟨7,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨7,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell8 :
    0 ≤ cap12269 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨8,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12269 ⟨8,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨8,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell9 :
    0 ≤ cap12269 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨9,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12269 ⟨9,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨9,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell10 :
    0 ≤ cap12269 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨10,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12269 ⟨10,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨10,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell11 :
    0 ≤ cap12269 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨11,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12269 ⟨11,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨11,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell12 :
    0 ≤ cap12269 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨12,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12269 ⟨12,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨12,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell13 :
    0 ≤ cap12269 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨13,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12269 ⟨13,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨13,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell14 :
    0 ≤ cap12269 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨14,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12269 ⟨14,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨14,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell15 :
    0 ≤ cap12269 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨15,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12269 ⟨15,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨15,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell16 :
    0 ≤ cap12269 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨16,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12269 ⟨16,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨16,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell17 :
    0 ≤ cap12269 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨17,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12269 ⟨17,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨17,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell18 :
    0 ≤ cap12269 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨18,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12269 ⟨18,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨18,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell19 :
    0 ≤ cap12269 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨19,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12269 ⟨19,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨19,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell20 :
    0 ≤ cap12269 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨20,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12269 ⟨20,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨20,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell21 :
    0 ≤ cap12269 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨21,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12269 ⟨21,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨21,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell22 :
    0 ≤ cap12269 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨22,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12269 ⟨22,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨22,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell23 :
    0 ≤ cap12269 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨23,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12269 ⟨23,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨23,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell24 :
    0 ≤ cap12269 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨24,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12269 ⟨24,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨24,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell25 :
    0 ≤ cap12269 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨25,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12269 ⟨25,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨25,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell26 :
    0 ≤ cap12269 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨26,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12269 ⟨26,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨26,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell27 :
    0 ≤ cap12269 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨27,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12269 ⟨27,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨27,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell28 :
    0 ≤ cap12269 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨28,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12269 ⟨28,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨28,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell29 :
    0 ≤ cap12269 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨29,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12269 ⟨29,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨29,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell30 :
    0 ≤ cap12269 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨30,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12269 ⟨30,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨30,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell31 :
    0 ≤ cap12269 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨31,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12269 ⟨31,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨31,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell32 :
    0 ≤ cap12269 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨32,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12269 ⟨32,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨32,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell33 :
    0 ≤ cap12269 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨33,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12269 ⟨33,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨33,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell34 :
    0 ≤ cap12269 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨34,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12269 ⟨34,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨34,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell35 :
    0 ≤ cap12269 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨35,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12269 ⟨35,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨35,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell36 :
    0 ≤ cap12269 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨36,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12269 ⟨36,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨36,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell37 :
    0 ≤ cap12269 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨37,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12269 ⟨37,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨37,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell38 :
    0 ≤ cap12269 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨38,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12269 ⟨38,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨38,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell39 :
    0 ≤ cap12269 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨39,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12269 ⟨39,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨39,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell40 :
    0 ≤ cap12269 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨40,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12269 ⟨40,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨40,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell41 :
    0 ≤ cap12269 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨41,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12269 ⟨41,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨41,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cell42 :
    0 ≤ cap12269 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12269 (parameters ⟨42,by decide⟩)
      (scalarRow12269.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12269 ⟨42,by decide⟩ ∧
    (scalarRow12269.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 ⟨42,by decide⟩ + (scalarRow12269.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12269.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12269.targetFrame := by
  norm_num [cap12269, scalarRow12269, sourceIndex, cell12269, BstLean.Part263.envelope, parameters]

theorem repair12269Cells (j : Fin 43) :
    0 ≤ cap12269 j ∧
    BstLean.Part263.envelope 12269 (parameters j) (scalarRow12269.table (sourceIndex j)).upper ≤ cap12269 j ∧
    (scalarRow12269.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12269 j + (scalarRow12269.table (sourceIndex j)).centre) /
      (scalarRow12269.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12269.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12269Cell0
  | ⟨1,_⟩ => exact repair12269Cell1
  | ⟨2,_⟩ => exact repair12269Cell2
  | ⟨3,_⟩ => exact repair12269Cell3
  | ⟨4,_⟩ => exact repair12269Cell4
  | ⟨5,_⟩ => exact repair12269Cell5
  | ⟨6,_⟩ => exact repair12269Cell6
  | ⟨7,_⟩ => exact repair12269Cell7
  | ⟨8,_⟩ => exact repair12269Cell8
  | ⟨9,_⟩ => exact repair12269Cell9
  | ⟨10,_⟩ => exact repair12269Cell10
  | ⟨11,_⟩ => exact repair12269Cell11
  | ⟨12,_⟩ => exact repair12269Cell12
  | ⟨13,_⟩ => exact repair12269Cell13
  | ⟨14,_⟩ => exact repair12269Cell14
  | ⟨15,_⟩ => exact repair12269Cell15
  | ⟨16,_⟩ => exact repair12269Cell16
  | ⟨17,_⟩ => exact repair12269Cell17
  | ⟨18,_⟩ => exact repair12269Cell18
  | ⟨19,_⟩ => exact repair12269Cell19
  | ⟨20,_⟩ => exact repair12269Cell20
  | ⟨21,_⟩ => exact repair12269Cell21
  | ⟨22,_⟩ => exact repair12269Cell22
  | ⟨23,_⟩ => exact repair12269Cell23
  | ⟨24,_⟩ => exact repair12269Cell24
  | ⟨25,_⟩ => exact repair12269Cell25
  | ⟨26,_⟩ => exact repair12269Cell26
  | ⟨27,_⟩ => exact repair12269Cell27
  | ⟨28,_⟩ => exact repair12269Cell28
  | ⟨29,_⟩ => exact repair12269Cell29
  | ⟨30,_⟩ => exact repair12269Cell30
  | ⟨31,_⟩ => exact repair12269Cell31
  | ⟨32,_⟩ => exact repair12269Cell32
  | ⟨33,_⟩ => exact repair12269Cell33
  | ⟨34,_⟩ => exact repair12269Cell34
  | ⟨35,_⟩ => exact repair12269Cell35
  | ⟨36,_⟩ => exact repair12269Cell36
  | ⟨37,_⟩ => exact repair12269Cell37
  | ⟨38,_⟩ => exact repair12269Cell38
  | ⟨39,_⟩ => exact repair12269Cell39
  | ⟨40,_⟩ => exact repair12269Cell40
  | ⟨41,_⟩ => exact repair12269Cell41
  | ⟨42,_⟩ => exact repair12269Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12269 : FrameRepair 12269 scalarRow12269 where
  cap := cap12269
  cap_nonneg := fun j => (repair12269Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12269])
  endpoint := fun j => (repair12269Cells j).2.1
  endpoint_upper := fun j => (repair12269Cells j).2.2.1
  frame := fun j => (repair12269Cells j).2.2.2

noncomputable def cap12270 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275949321 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (2763523 / 10000000 : ℝ)
  | ⟨2,_⟩ => (55350857 / 200000000 : ℝ)
  | ⟨3,_⟩ => (34644409 / 125000000 : ℝ)
  | ⟨4,_⟩ => (69388817 / 250000000 : ℝ)
  | ⟨5,_⟩ => (138977137 / 500000000 : ℝ)
  | ⟨6,_⟩ => (278351819 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (139374429 / 500000000 : ℝ)
  | ⟨8,_⟩ => (6978623 / 25000000 : ℝ)
  | ⟨9,_⟩ => (27954001 / 100000000 : ℝ)
  | ⟨10,_⟩ => (17495883 / 62500000 : ℝ)
  | ⟨11,_⟩ => (140163399 / 500000000 : ℝ)
  | ⟨12,_⟩ => (28071899 / 100000000 : ℝ)
  | ⟨13,_⟩ => (56221947 / 200000000 : ℝ)
  | ⟨14,_⟩ => (281500413 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (28188999 / 100000000 : ℝ)
  | ⟨16,_⟩ => (8821207 / 31250000 : ℝ)
  | ⟨17,_⟩ => (282666327 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (28305309 / 100000000 : ℝ)
  | ⟨19,_⟩ => (11337557 / 40000000 : ℝ)
  | ⟨20,_⟩ => (35477979 / 125000000 : ℝ)
  | ⟨21,_⟩ => (142103911 / 500000000 : ℝ)
  | ⟨22,_⟩ => (35573861 / 125000000 : ℝ)
  | ⟨23,_⟩ => (284972543 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (142676893 / 500000000 : ℝ)
  | ⟨25,_⟩ => (142866833 / 500000000 : ℝ)
  | ⟨26,_⟩ => (143056571 / 500000000 : ℝ)
  | ⟨27,_⟩ => (286491219 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (143434199 / 500000000 : ℝ)
  | ⟨29,_⟩ => (143622341 / 500000000 : ℝ)
  | ⟨30,_⟩ => (71904893 / 250000000 : ℝ)
  | ⟨31,_⟩ => (287994077 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288367701 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144369967 / 500000000 : ℝ)
  | ⟨34,_⟩ => (72277823 / 250000000 : ℝ)
  | ⟨35,_⟩ => (289481779 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (72462847 / 250000000 : ℝ)
  | ⟨37,_⟩ => (290220137 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145294011 / 500000000 : ℝ)
  | ⟨39,_⟩ => (290954533 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (58264037 / 200000000 : ℝ)
  | ⟨41,_⟩ => (145842493 / 500000000 : ℝ)
  | ⟨42,_⟩ => (146024467 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12270Cell0 :
    0 ≤ cap12270 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨0,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12270 ⟨0,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨0,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell1 :
    0 ≤ cap12270 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨1,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12270 ⟨1,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨1,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell2 :
    0 ≤ cap12270 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨2,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12270 ⟨2,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨2,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell3 :
    0 ≤ cap12270 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨3,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12270 ⟨3,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨3,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell4 :
    0 ≤ cap12270 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨4,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12270 ⟨4,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨4,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell5 :
    0 ≤ cap12270 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨5,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12270 ⟨5,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨5,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell6 :
    0 ≤ cap12270 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨6,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12270 ⟨6,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨6,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell7 :
    0 ≤ cap12270 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨7,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12270 ⟨7,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨7,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell8 :
    0 ≤ cap12270 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨8,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12270 ⟨8,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨8,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell9 :
    0 ≤ cap12270 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨9,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12270 ⟨9,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨9,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell10 :
    0 ≤ cap12270 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨10,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12270 ⟨10,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨10,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell11 :
    0 ≤ cap12270 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨11,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12270 ⟨11,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨11,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell12 :
    0 ≤ cap12270 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨12,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12270 ⟨12,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨12,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell13 :
    0 ≤ cap12270 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨13,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12270 ⟨13,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨13,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell14 :
    0 ≤ cap12270 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨14,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12270 ⟨14,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨14,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell15 :
    0 ≤ cap12270 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨15,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12270 ⟨15,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨15,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell16 :
    0 ≤ cap12270 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨16,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12270 ⟨16,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨16,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell17 :
    0 ≤ cap12270 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨17,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12270 ⟨17,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨17,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell18 :
    0 ≤ cap12270 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨18,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12270 ⟨18,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨18,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell19 :
    0 ≤ cap12270 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨19,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12270 ⟨19,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨19,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell20 :
    0 ≤ cap12270 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨20,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12270 ⟨20,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨20,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell21 :
    0 ≤ cap12270 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨21,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12270 ⟨21,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨21,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell22 :
    0 ≤ cap12270 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨22,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12270 ⟨22,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨22,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell23 :
    0 ≤ cap12270 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨23,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12270 ⟨23,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨23,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell24 :
    0 ≤ cap12270 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨24,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12270 ⟨24,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨24,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell25 :
    0 ≤ cap12270 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨25,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12270 ⟨25,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨25,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell26 :
    0 ≤ cap12270 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨26,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12270 ⟨26,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨26,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell27 :
    0 ≤ cap12270 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨27,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12270 ⟨27,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨27,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell28 :
    0 ≤ cap12270 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨28,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12270 ⟨28,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨28,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell29 :
    0 ≤ cap12270 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨29,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12270 ⟨29,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨29,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell30 :
    0 ≤ cap12270 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨30,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12270 ⟨30,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨30,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell31 :
    0 ≤ cap12270 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨31,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12270 ⟨31,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨31,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell32 :
    0 ≤ cap12270 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨32,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12270 ⟨32,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨32,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell33 :
    0 ≤ cap12270 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨33,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12270 ⟨33,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨33,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell34 :
    0 ≤ cap12270 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨34,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12270 ⟨34,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨34,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell35 :
    0 ≤ cap12270 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨35,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12270 ⟨35,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨35,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell36 :
    0 ≤ cap12270 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨36,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12270 ⟨36,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨36,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell37 :
    0 ≤ cap12270 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨37,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12270 ⟨37,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨37,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell38 :
    0 ≤ cap12270 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨38,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12270 ⟨38,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨38,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell39 :
    0 ≤ cap12270 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨39,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12270 ⟨39,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨39,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell40 :
    0 ≤ cap12270 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨40,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12270 ⟨40,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨40,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell41 :
    0 ≤ cap12270 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨41,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12270 ⟨41,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨41,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cell42 :
    0 ≤ cap12270 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12270 (parameters ⟨42,by decide⟩)
      (scalarRow12270.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12270 ⟨42,by decide⟩ ∧
    (scalarRow12270.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 ⟨42,by decide⟩ + (scalarRow12270.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12270.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12270.targetFrame := by
  norm_num [cap12270, scalarRow12270, sourceIndex, cell12270, BstLean.Part263.envelope, parameters]

theorem repair12270Cells (j : Fin 43) :
    0 ≤ cap12270 j ∧
    BstLean.Part263.envelope 12270 (parameters j) (scalarRow12270.table (sourceIndex j)).upper ≤ cap12270 j ∧
    (scalarRow12270.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12270 j + (scalarRow12270.table (sourceIndex j)).centre) /
      (scalarRow12270.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12270.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12270Cell0
  | ⟨1,_⟩ => exact repair12270Cell1
  | ⟨2,_⟩ => exact repair12270Cell2
  | ⟨3,_⟩ => exact repair12270Cell3
  | ⟨4,_⟩ => exact repair12270Cell4
  | ⟨5,_⟩ => exact repair12270Cell5
  | ⟨6,_⟩ => exact repair12270Cell6
  | ⟨7,_⟩ => exact repair12270Cell7
  | ⟨8,_⟩ => exact repair12270Cell8
  | ⟨9,_⟩ => exact repair12270Cell9
  | ⟨10,_⟩ => exact repair12270Cell10
  | ⟨11,_⟩ => exact repair12270Cell11
  | ⟨12,_⟩ => exact repair12270Cell12
  | ⟨13,_⟩ => exact repair12270Cell13
  | ⟨14,_⟩ => exact repair12270Cell14
  | ⟨15,_⟩ => exact repair12270Cell15
  | ⟨16,_⟩ => exact repair12270Cell16
  | ⟨17,_⟩ => exact repair12270Cell17
  | ⟨18,_⟩ => exact repair12270Cell18
  | ⟨19,_⟩ => exact repair12270Cell19
  | ⟨20,_⟩ => exact repair12270Cell20
  | ⟨21,_⟩ => exact repair12270Cell21
  | ⟨22,_⟩ => exact repair12270Cell22
  | ⟨23,_⟩ => exact repair12270Cell23
  | ⟨24,_⟩ => exact repair12270Cell24
  | ⟨25,_⟩ => exact repair12270Cell25
  | ⟨26,_⟩ => exact repair12270Cell26
  | ⟨27,_⟩ => exact repair12270Cell27
  | ⟨28,_⟩ => exact repair12270Cell28
  | ⟨29,_⟩ => exact repair12270Cell29
  | ⟨30,_⟩ => exact repair12270Cell30
  | ⟨31,_⟩ => exact repair12270Cell31
  | ⟨32,_⟩ => exact repair12270Cell32
  | ⟨33,_⟩ => exact repair12270Cell33
  | ⟨34,_⟩ => exact repair12270Cell34
  | ⟨35,_⟩ => exact repair12270Cell35
  | ⟨36,_⟩ => exact repair12270Cell36
  | ⟨37,_⟩ => exact repair12270Cell37
  | ⟨38,_⟩ => exact repair12270Cell38
  | ⟨39,_⟩ => exact repair12270Cell39
  | ⟨40,_⟩ => exact repair12270Cell40
  | ⟨41,_⟩ => exact repair12270Cell41
  | ⟨42,_⟩ => exact repair12270Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12270 : FrameRepair 12270 scalarRow12270 where
  cap := cap12270
  cap_nonneg := fun j => (repair12270Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12270])
  endpoint := fun j => (repair12270Cells j).2.1
  endpoint_upper := fun j => (repair12270Cells j).2.2.1
  frame := fun j => (repair12270Cells j).2.2.2

noncomputable def cap12271 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137974623 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138176109 / 500000000 : ℝ)
  | ⟨2,_⟩ => (276754197 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (277155177 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (277555167 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (138977083 / 500000000 : ℝ)
  | ⟨6,_⟩ => (55670341 / 200000000 : ℝ)
  | ⟨7,_⟩ => (278748737 / 1000000000 : ℝ)
  | ⟨8,_⟩ => (279144793 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69884969 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279933989 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (70081663 / 250000000 : ℝ)
  | ⟨12,_⟩ => (140359419 / 500000000 : ℝ)
  | ⟨13,_⟩ => (35138697 / 125000000 : ℝ)
  | ⟨14,_⟩ => (35187531 / 125000000 : ℝ)
  | ⟨15,_⟩ => (281889819 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282278447 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282666143 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (2830529 / 10000000 : ℝ)
  | ⟨19,_⟩ => (35429841 / 125000000 : ℝ)
  | ⟨20,_⟩ => (283823629 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (284207613 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (284590673 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142486161 / 500000000 : ℝ)
  | ⟨24,_⟩ => (142676779 / 500000000 : ℝ)
  | ⟨25,_⟩ => (35716679 / 125000000 : ℝ)
  | ⟨26,_⟩ => (143056451 / 500000000 : ℝ)
  | ⟨27,_⟩ => (71622743 / 250000000 : ℝ)
  | ⟨28,_⟩ => (143434073 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287244423 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287619307 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (143996903 / 500000000 : ℝ)
  | ⟨32,_⟩ => (4505741 / 15625000 : ℝ)
  | ⟨33,_⟩ => (72184913 / 250000000 : ℝ)
  | ⟨34,_⟩ => (72277751 / 250000000 : ℝ)
  | ⟨35,_⟩ => (72370371 / 250000000 : ℝ)
  | ⟨36,_⟩ => (289851087 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (290219831 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290587709 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145477107 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291319861 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (58336931 / 200000000 : ℝ)
  | ⟨42,_⟩ => (146024299 / 500000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12271Cell0 :
    0 ≤ cap12271 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨0,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12271 ⟨0,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨0,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell1 :
    0 ≤ cap12271 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨1,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12271 ⟨1,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨1,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell2 :
    0 ≤ cap12271 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨2,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12271 ⟨2,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨2,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell3 :
    0 ≤ cap12271 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨3,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12271 ⟨3,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨3,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell4 :
    0 ≤ cap12271 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨4,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12271 ⟨4,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨4,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell5 :
    0 ≤ cap12271 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨5,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12271 ⟨5,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨5,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell6 :
    0 ≤ cap12271 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨6,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12271 ⟨6,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨6,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell7 :
    0 ≤ cap12271 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨7,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12271 ⟨7,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨7,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell8 :
    0 ≤ cap12271 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨8,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12271 ⟨8,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨8,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell9 :
    0 ≤ cap12271 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨9,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12271 ⟨9,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨9,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell10 :
    0 ≤ cap12271 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨10,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12271 ⟨10,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨10,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell11 :
    0 ≤ cap12271 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨11,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12271 ⟨11,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨11,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell12 :
    0 ≤ cap12271 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨12,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12271 ⟨12,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨12,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell13 :
    0 ≤ cap12271 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨13,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12271 ⟨13,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨13,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell14 :
    0 ≤ cap12271 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨14,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12271 ⟨14,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨14,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell15 :
    0 ≤ cap12271 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨15,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12271 ⟨15,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨15,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell16 :
    0 ≤ cap12271 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨16,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12271 ⟨16,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨16,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell17 :
    0 ≤ cap12271 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨17,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12271 ⟨17,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨17,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell18 :
    0 ≤ cap12271 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨18,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12271 ⟨18,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨18,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell19 :
    0 ≤ cap12271 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨19,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12271 ⟨19,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨19,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell20 :
    0 ≤ cap12271 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨20,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12271 ⟨20,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨20,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell21 :
    0 ≤ cap12271 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨21,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12271 ⟨21,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨21,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell22 :
    0 ≤ cap12271 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨22,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12271 ⟨22,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨22,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell23 :
    0 ≤ cap12271 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨23,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12271 ⟨23,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨23,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell24 :
    0 ≤ cap12271 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨24,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12271 ⟨24,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨24,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell25 :
    0 ≤ cap12271 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨25,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12271 ⟨25,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨25,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell26 :
    0 ≤ cap12271 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨26,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12271 ⟨26,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨26,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell27 :
    0 ≤ cap12271 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨27,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12271 ⟨27,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨27,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell28 :
    0 ≤ cap12271 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨28,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12271 ⟨28,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨28,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell29 :
    0 ≤ cap12271 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨29,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12271 ⟨29,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨29,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell30 :
    0 ≤ cap12271 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨30,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12271 ⟨30,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨30,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell31 :
    0 ≤ cap12271 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨31,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12271 ⟨31,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨31,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell32 :
    0 ≤ cap12271 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨32,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12271 ⟨32,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨32,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell33 :
    0 ≤ cap12271 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨33,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12271 ⟨33,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨33,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell34 :
    0 ≤ cap12271 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨34,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12271 ⟨34,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨34,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell35 :
    0 ≤ cap12271 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨35,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12271 ⟨35,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨35,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell36 :
    0 ≤ cap12271 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨36,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12271 ⟨36,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨36,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell37 :
    0 ≤ cap12271 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨37,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12271 ⟨37,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨37,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell38 :
    0 ≤ cap12271 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨38,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12271 ⟨38,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨38,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell39 :
    0 ≤ cap12271 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨39,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12271 ⟨39,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨39,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell40 :
    0 ≤ cap12271 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨40,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12271 ⟨40,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨40,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell41 :
    0 ≤ cap12271 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨41,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12271 ⟨41,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨41,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cell42 :
    0 ≤ cap12271 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12271 (parameters ⟨42,by decide⟩)
      (scalarRow12271.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12271 ⟨42,by decide⟩ ∧
    (scalarRow12271.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 ⟨42,by decide⟩ + (scalarRow12271.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12271.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12271.targetFrame := by
  norm_num [cap12271, scalarRow12271, sourceIndex, cell12271, BstLean.Part263.envelope, parameters]

theorem repair12271Cells (j : Fin 43) :
    0 ≤ cap12271 j ∧
    BstLean.Part263.envelope 12271 (parameters j) (scalarRow12271.table (sourceIndex j)).upper ≤ cap12271 j ∧
    (scalarRow12271.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12271 j + (scalarRow12271.table (sourceIndex j)).centre) /
      (scalarRow12271.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12271.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12271Cell0
  | ⟨1,_⟩ => exact repair12271Cell1
  | ⟨2,_⟩ => exact repair12271Cell2
  | ⟨3,_⟩ => exact repair12271Cell3
  | ⟨4,_⟩ => exact repair12271Cell4
  | ⟨5,_⟩ => exact repair12271Cell5
  | ⟨6,_⟩ => exact repair12271Cell6
  | ⟨7,_⟩ => exact repair12271Cell7
  | ⟨8,_⟩ => exact repair12271Cell8
  | ⟨9,_⟩ => exact repair12271Cell9
  | ⟨10,_⟩ => exact repair12271Cell10
  | ⟨11,_⟩ => exact repair12271Cell11
  | ⟨12,_⟩ => exact repair12271Cell12
  | ⟨13,_⟩ => exact repair12271Cell13
  | ⟨14,_⟩ => exact repair12271Cell14
  | ⟨15,_⟩ => exact repair12271Cell15
  | ⟨16,_⟩ => exact repair12271Cell16
  | ⟨17,_⟩ => exact repair12271Cell17
  | ⟨18,_⟩ => exact repair12271Cell18
  | ⟨19,_⟩ => exact repair12271Cell19
  | ⟨20,_⟩ => exact repair12271Cell20
  | ⟨21,_⟩ => exact repair12271Cell21
  | ⟨22,_⟩ => exact repair12271Cell22
  | ⟨23,_⟩ => exact repair12271Cell23
  | ⟨24,_⟩ => exact repair12271Cell24
  | ⟨25,_⟩ => exact repair12271Cell25
  | ⟨26,_⟩ => exact repair12271Cell26
  | ⟨27,_⟩ => exact repair12271Cell27
  | ⟨28,_⟩ => exact repair12271Cell28
  | ⟨29,_⟩ => exact repair12271Cell29
  | ⟨30,_⟩ => exact repair12271Cell30
  | ⟨31,_⟩ => exact repair12271Cell31
  | ⟨32,_⟩ => exact repair12271Cell32
  | ⟨33,_⟩ => exact repair12271Cell33
  | ⟨34,_⟩ => exact repair12271Cell34
  | ⟨35,_⟩ => exact repair12271Cell35
  | ⟨36,_⟩ => exact repair12271Cell36
  | ⟨37,_⟩ => exact repair12271Cell37
  | ⟨38,_⟩ => exact repair12271Cell38
  | ⟨39,_⟩ => exact repair12271Cell39
  | ⟨40,_⟩ => exact repair12271Cell40
  | ⟨41,_⟩ => exact repair12271Cell41
  | ⟨42,_⟩ => exact repair12271Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12271 : FrameRepair 12271 scalarRow12271 where
  cap := cap12271
  cap_nonneg := fun j => (repair12271Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12271])
  endpoint := fun j => (repair12271Cells j).2.1
  endpoint_upper := fun j => (repair12271Cells j).2.2.1
  frame := fun j => (repair12271Cells j).2.2.2

noncomputable def cap12272 : Fin 43 → ℝ
  | ⟨0,_⟩ => (27594917 / 100000000 : ℝ)
  | ⟨1,_⟩ => (34544017 / 125000000 : ℝ)
  | ⟨2,_⟩ => (69188527 / 250000000 : ℝ)
  | ⟨3,_⟩ => (138577541 / 500000000 : ℝ)
  | ⟨4,_⟩ => (55511013 / 200000000 : ℝ)
  | ⟨5,_⟩ => (138977029 / 500000000 : ℝ)
  | ⟨6,_⟩ => (27835159 / 100000000 : ℝ)
  | ⟨7,_⟩ => (34843577 / 125000000 : ℝ)
  | ⟨8,_⟩ => (139572333 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279539743 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279933849 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (140163253 / 500000000 : ℝ)
  | ⟨12,_⟩ => (56143737 / 200000000 : ℝ)
  | ⟨13,_⟩ => (281109417 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (140750041 / 500000000 : ℝ)
  | ⟨15,_⟩ => (281889647 / 1000000000 : ℝ)
  | ⟨16,_⟩ => (282278269 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282665959 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (28305271 / 100000000 : ℝ)
  | ⟨19,_⟩ => (70859633 / 250000000 : ℝ)
  | ⟨20,_⟩ => (141911713 / 500000000 : ℝ)
  | ⟨21,_⟩ => (71051851 / 250000000 : ℝ)
  | ⟨22,_⟩ => (142295229 / 500000000 : ℝ)
  | ⟨23,_⟩ => (2849721 / 10000000 : ℝ)
  | ⟨24,_⟩ => (28535333 / 100000000 : ℝ)
  | ⟨25,_⟩ => (285733199 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (143056331 / 500000000 : ℝ)
  | ⟨27,_⟩ => (143245363 / 500000000 : ℝ)
  | ⟨28,_⟩ => (143433947 / 500000000 : ℝ)
  | ⟨29,_⟩ => (57448833 / 200000000 : ℝ)
  | ⟨30,_⟩ => (287619043 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (4499899 / 15625000 : ℝ)
  | ⟨32,_⟩ => (72091787 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288739369 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (57822143 / 200000000 : ℝ)
  | ⟨35,_⟩ => (289481189 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144925393 / 500000000 : ℝ)
  | ⟨37,_⟩ => (72554881 / 250000000 : ℝ)
  | ⟨38,_⟩ => (72646849 / 250000000 : ℝ)
  | ⟨39,_⟩ => (58190779 / 200000000 : ℝ)
  | ⟨40,_⟩ => (18207471 / 62500000 : ℝ)
  | ⟨41,_⟩ => (72921081 / 250000000 : ℝ)
  | ⟨42,_⟩ => (292048261 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12272Cell0 :
    0 ≤ cap12272 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨0,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12272 ⟨0,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨0,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell1 :
    0 ≤ cap12272 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨1,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12272 ⟨1,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨1,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell2 :
    0 ≤ cap12272 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨2,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12272 ⟨2,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨2,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell3 :
    0 ≤ cap12272 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨3,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12272 ⟨3,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨3,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell4 :
    0 ≤ cap12272 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨4,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12272 ⟨4,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨4,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell5 :
    0 ≤ cap12272 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨5,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12272 ⟨5,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨5,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell6 :
    0 ≤ cap12272 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨6,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12272 ⟨6,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨6,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell7 :
    0 ≤ cap12272 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨7,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12272 ⟨7,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨7,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell8 :
    0 ≤ cap12272 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨8,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12272 ⟨8,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨8,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell9 :
    0 ≤ cap12272 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨9,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12272 ⟨9,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨9,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell10 :
    0 ≤ cap12272 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨10,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12272 ⟨10,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨10,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell11 :
    0 ≤ cap12272 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨11,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12272 ⟨11,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨11,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell12 :
    0 ≤ cap12272 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨12,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12272 ⟨12,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨12,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell13 :
    0 ≤ cap12272 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨13,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12272 ⟨13,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨13,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell14 :
    0 ≤ cap12272 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨14,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12272 ⟨14,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨14,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell15 :
    0 ≤ cap12272 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨15,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12272 ⟨15,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨15,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell16 :
    0 ≤ cap12272 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨16,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12272 ⟨16,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨16,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell17 :
    0 ≤ cap12272 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨17,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12272 ⟨17,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨17,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell18 :
    0 ≤ cap12272 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨18,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12272 ⟨18,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨18,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell19 :
    0 ≤ cap12272 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨19,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12272 ⟨19,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨19,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell20 :
    0 ≤ cap12272 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨20,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12272 ⟨20,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨20,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell21 :
    0 ≤ cap12272 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨21,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12272 ⟨21,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨21,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell22 :
    0 ≤ cap12272 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨22,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12272 ⟨22,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨22,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell23 :
    0 ≤ cap12272 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨23,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12272 ⟨23,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨23,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell24 :
    0 ≤ cap12272 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨24,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12272 ⟨24,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨24,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell25 :
    0 ≤ cap12272 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨25,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12272 ⟨25,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨25,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell26 :
    0 ≤ cap12272 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨26,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12272 ⟨26,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨26,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell27 :
    0 ≤ cap12272 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨27,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12272 ⟨27,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨27,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell28 :
    0 ≤ cap12272 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨28,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12272 ⟨28,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨28,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell29 :
    0 ≤ cap12272 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨29,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12272 ⟨29,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨29,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell30 :
    0 ≤ cap12272 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨30,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12272 ⟨30,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨30,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell31 :
    0 ≤ cap12272 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨31,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12272 ⟨31,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨31,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell32 :
    0 ≤ cap12272 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨32,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12272 ⟨32,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨32,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell33 :
    0 ≤ cap12272 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨33,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12272 ⟨33,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨33,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell34 :
    0 ≤ cap12272 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨34,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12272 ⟨34,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨34,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell35 :
    0 ≤ cap12272 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨35,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12272 ⟨35,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨35,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell36 :
    0 ≤ cap12272 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨36,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12272 ⟨36,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨36,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell37 :
    0 ≤ cap12272 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨37,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12272 ⟨37,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨37,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell38 :
    0 ≤ cap12272 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨38,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12272 ⟨38,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨38,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell39 :
    0 ≤ cap12272 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨39,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12272 ⟨39,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨39,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell40 :
    0 ≤ cap12272 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨40,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12272 ⟨40,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨40,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell41 :
    0 ≤ cap12272 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨41,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12272 ⟨41,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨41,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cell42 :
    0 ≤ cap12272 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12272 (parameters ⟨42,by decide⟩)
      (scalarRow12272.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12272 ⟨42,by decide⟩ ∧
    (scalarRow12272.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 ⟨42,by decide⟩ + (scalarRow12272.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12272.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12272.targetFrame := by
  norm_num [cap12272, scalarRow12272, sourceIndex, cell12272, BstLean.Part263.envelope, parameters]

theorem repair12272Cells (j : Fin 43) :
    0 ≤ cap12272 j ∧
    BstLean.Part263.envelope 12272 (parameters j) (scalarRow12272.table (sourceIndex j)).upper ≤ cap12272 j ∧
    (scalarRow12272.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12272 j + (scalarRow12272.table (sourceIndex j)).centre) /
      (scalarRow12272.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12272.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12272Cell0
  | ⟨1,_⟩ => exact repair12272Cell1
  | ⟨2,_⟩ => exact repair12272Cell2
  | ⟨3,_⟩ => exact repair12272Cell3
  | ⟨4,_⟩ => exact repair12272Cell4
  | ⟨5,_⟩ => exact repair12272Cell5
  | ⟨6,_⟩ => exact repair12272Cell6
  | ⟨7,_⟩ => exact repair12272Cell7
  | ⟨8,_⟩ => exact repair12272Cell8
  | ⟨9,_⟩ => exact repair12272Cell9
  | ⟨10,_⟩ => exact repair12272Cell10
  | ⟨11,_⟩ => exact repair12272Cell11
  | ⟨12,_⟩ => exact repair12272Cell12
  | ⟨13,_⟩ => exact repair12272Cell13
  | ⟨14,_⟩ => exact repair12272Cell14
  | ⟨15,_⟩ => exact repair12272Cell15
  | ⟨16,_⟩ => exact repair12272Cell16
  | ⟨17,_⟩ => exact repair12272Cell17
  | ⟨18,_⟩ => exact repair12272Cell18
  | ⟨19,_⟩ => exact repair12272Cell19
  | ⟨20,_⟩ => exact repair12272Cell20
  | ⟨21,_⟩ => exact repair12272Cell21
  | ⟨22,_⟩ => exact repair12272Cell22
  | ⟨23,_⟩ => exact repair12272Cell23
  | ⟨24,_⟩ => exact repair12272Cell24
  | ⟨25,_⟩ => exact repair12272Cell25
  | ⟨26,_⟩ => exact repair12272Cell26
  | ⟨27,_⟩ => exact repair12272Cell27
  | ⟨28,_⟩ => exact repair12272Cell28
  | ⟨29,_⟩ => exact repair12272Cell29
  | ⟨30,_⟩ => exact repair12272Cell30
  | ⟨31,_⟩ => exact repair12272Cell31
  | ⟨32,_⟩ => exact repair12272Cell32
  | ⟨33,_⟩ => exact repair12272Cell33
  | ⟨34,_⟩ => exact repair12272Cell34
  | ⟨35,_⟩ => exact repair12272Cell35
  | ⟨36,_⟩ => exact repair12272Cell36
  | ⟨37,_⟩ => exact repair12272Cell37
  | ⟨38,_⟩ => exact repair12272Cell38
  | ⟨39,_⟩ => exact repair12272Cell39
  | ⟨40,_⟩ => exact repair12272Cell40
  | ⟨41,_⟩ => exact repair12272Cell41
  | ⟨42,_⟩ => exact repair12272Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12272 : FrameRepair 12272 scalarRow12272 where
  cap := cap12272
  cap_nonneg := fun j => (repair12272Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12272])
  endpoint := fun j => (repair12272Cells j).2.1
  endpoint_upper := fun j => (repair12272Cells j).2.2.1
  frame := fun j => (repair12272Cells j).2.2.2

noncomputable def cap12273 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137974547 / 500000000 : ℝ)
  | ⟨1,_⟩ => (138176027 / 500000000 : ℝ)
  | ⟨2,_⟩ => (13837701 / 50000000 : ℝ)
  | ⟨3,_⟩ => (277154987 / 1000000000 : ℝ)
  | ⟨4,_⟩ => (69388741 / 250000000 : ℝ)
  | ⟨5,_⟩ => (5559079 / 20000000 : ℝ)
  | ⟨6,_⟩ => (69587869 / 250000000 : ℝ)
  | ⟨7,_⟩ => (55749699 / 200000000 : ℝ)
  | ⟨8,_⟩ => (279144539 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (279539609 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279933709 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (7008159 / 25000000 : ℝ)
  | ⟨12,_⟩ => (280718533 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (281109259 / 1000000000 : ℝ)
  | ⟨14,_⟩ => (281499917 / 1000000000 : ℝ)
  | ⟨15,_⟩ => (70472369 / 250000000 : ℝ)
  | ⟨16,_⟩ => (282278091 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (11306631 / 40000000 : ℝ)
  | ⟨18,_⟩ => (283052519 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (56687667 / 200000000 : ℝ)
  | ⟨20,_⟩ => (283823223 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56841439 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284590243 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (284971879 / 1000000000 : ℝ)
  | ⟨24,_⟩ => (285353103 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (57146593 / 200000000 : ℝ)
  | ⟨26,_⟩ => (143056211 / 500000000 : ℝ)
  | ⟨27,_⟩ => (3581131 / 12500000 : ℝ)
  | ⟨28,_⟩ => (143433821 / 500000000 : ℝ)
  | ⟨29,_⟩ => (287243907 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143809389 / 500000000 : ℝ)
  | ⟨31,_⟩ => (57598653 / 200000000 : ℝ)
  | ⟨32,_⟩ => (288366871 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (144369543 / 500000000 : ℝ)
  | ⟨34,_⟩ => (144555213 / 500000000 : ℝ)
  | ⟨35,_⟩ => (144740447 / 500000000 : ℝ)
  | ⟨36,_⟩ => (57970097 / 200000000 : ℝ)
  | ⟨37,_⟩ => (290219217 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290587083 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (290953577 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291319211 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (145841997 / 500000000 : ℝ)
  | ⟨42,_⟩ => (73011981 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12273Cell0 :
    0 ≤ cap12273 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨0,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12273 ⟨0,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨0,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell1 :
    0 ≤ cap12273 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨1,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12273 ⟨1,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨1,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell2 :
    0 ≤ cap12273 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨2,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12273 ⟨2,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨2,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell3 :
    0 ≤ cap12273 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨3,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12273 ⟨3,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨3,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell4 :
    0 ≤ cap12273 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨4,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12273 ⟨4,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨4,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell5 :
    0 ≤ cap12273 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨5,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12273 ⟨5,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨5,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell6 :
    0 ≤ cap12273 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨6,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12273 ⟨6,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨6,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell7 :
    0 ≤ cap12273 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨7,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12273 ⟨7,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨7,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell8 :
    0 ≤ cap12273 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨8,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12273 ⟨8,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨8,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell9 :
    0 ≤ cap12273 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨9,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12273 ⟨9,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨9,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell10 :
    0 ≤ cap12273 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨10,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12273 ⟨10,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨10,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell11 :
    0 ≤ cap12273 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨11,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12273 ⟨11,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨11,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell12 :
    0 ≤ cap12273 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨12,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12273 ⟨12,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨12,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell13 :
    0 ≤ cap12273 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨13,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12273 ⟨13,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨13,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell14 :
    0 ≤ cap12273 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨14,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12273 ⟨14,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨14,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell15 :
    0 ≤ cap12273 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨15,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12273 ⟨15,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨15,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell16 :
    0 ≤ cap12273 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨16,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12273 ⟨16,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨16,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell17 :
    0 ≤ cap12273 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨17,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12273 ⟨17,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨17,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell18 :
    0 ≤ cap12273 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨18,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12273 ⟨18,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨18,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell19 :
    0 ≤ cap12273 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨19,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12273 ⟨19,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨19,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell20 :
    0 ≤ cap12273 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨20,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12273 ⟨20,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨20,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell21 :
    0 ≤ cap12273 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨21,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12273 ⟨21,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨21,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell22 :
    0 ≤ cap12273 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨22,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12273 ⟨22,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨22,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell23 :
    0 ≤ cap12273 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨23,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12273 ⟨23,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨23,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell24 :
    0 ≤ cap12273 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨24,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12273 ⟨24,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨24,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell25 :
    0 ≤ cap12273 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨25,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12273 ⟨25,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨25,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell26 :
    0 ≤ cap12273 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨26,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12273 ⟨26,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨26,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell27 :
    0 ≤ cap12273 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨27,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12273 ⟨27,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨27,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell28 :
    0 ≤ cap12273 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨28,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12273 ⟨28,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨28,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell29 :
    0 ≤ cap12273 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨29,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12273 ⟨29,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨29,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell30 :
    0 ≤ cap12273 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨30,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12273 ⟨30,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨30,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell31 :
    0 ≤ cap12273 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨31,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12273 ⟨31,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨31,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell32 :
    0 ≤ cap12273 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨32,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12273 ⟨32,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨32,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell33 :
    0 ≤ cap12273 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨33,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12273 ⟨33,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨33,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell34 :
    0 ≤ cap12273 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨34,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12273 ⟨34,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨34,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell35 :
    0 ≤ cap12273 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨35,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12273 ⟨35,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨35,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell36 :
    0 ≤ cap12273 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨36,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12273 ⟨36,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨36,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell37 :
    0 ≤ cap12273 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨37,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12273 ⟨37,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨37,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell38 :
    0 ≤ cap12273 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨38,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12273 ⟨38,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨38,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell39 :
    0 ≤ cap12273 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨39,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12273 ⟨39,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨39,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell40 :
    0 ≤ cap12273 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨40,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12273 ⟨40,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨40,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell41 :
    0 ≤ cap12273 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨41,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12273 ⟨41,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨41,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cell42 :
    0 ≤ cap12273 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12273 (parameters ⟨42,by decide⟩)
      (scalarRow12273.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12273 ⟨42,by decide⟩ ∧
    (scalarRow12273.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 ⟨42,by decide⟩ + (scalarRow12273.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12273.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12273.targetFrame := by
  norm_num [cap12273, scalarRow12273, sourceIndex, cell12273, BstLean.Part263.envelope, parameters]

theorem repair12273Cells (j : Fin 43) :
    0 ≤ cap12273 j ∧
    BstLean.Part263.envelope 12273 (parameters j) (scalarRow12273.table (sourceIndex j)).upper ≤ cap12273 j ∧
    (scalarRow12273.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12273 j + (scalarRow12273.table (sourceIndex j)).centre) /
      (scalarRow12273.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12273.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12273Cell0
  | ⟨1,_⟩ => exact repair12273Cell1
  | ⟨2,_⟩ => exact repair12273Cell2
  | ⟨3,_⟩ => exact repair12273Cell3
  | ⟨4,_⟩ => exact repair12273Cell4
  | ⟨5,_⟩ => exact repair12273Cell5
  | ⟨6,_⟩ => exact repair12273Cell6
  | ⟨7,_⟩ => exact repair12273Cell7
  | ⟨8,_⟩ => exact repair12273Cell8
  | ⟨9,_⟩ => exact repair12273Cell9
  | ⟨10,_⟩ => exact repair12273Cell10
  | ⟨11,_⟩ => exact repair12273Cell11
  | ⟨12,_⟩ => exact repair12273Cell12
  | ⟨13,_⟩ => exact repair12273Cell13
  | ⟨14,_⟩ => exact repair12273Cell14
  | ⟨15,_⟩ => exact repair12273Cell15
  | ⟨16,_⟩ => exact repair12273Cell16
  | ⟨17,_⟩ => exact repair12273Cell17
  | ⟨18,_⟩ => exact repair12273Cell18
  | ⟨19,_⟩ => exact repair12273Cell19
  | ⟨20,_⟩ => exact repair12273Cell20
  | ⟨21,_⟩ => exact repair12273Cell21
  | ⟨22,_⟩ => exact repair12273Cell22
  | ⟨23,_⟩ => exact repair12273Cell23
  | ⟨24,_⟩ => exact repair12273Cell24
  | ⟨25,_⟩ => exact repair12273Cell25
  | ⟨26,_⟩ => exact repair12273Cell26
  | ⟨27,_⟩ => exact repair12273Cell27
  | ⟨28,_⟩ => exact repair12273Cell28
  | ⟨29,_⟩ => exact repair12273Cell29
  | ⟨30,_⟩ => exact repair12273Cell30
  | ⟨31,_⟩ => exact repair12273Cell31
  | ⟨32,_⟩ => exact repair12273Cell32
  | ⟨33,_⟩ => exact repair12273Cell33
  | ⟨34,_⟩ => exact repair12273Cell34
  | ⟨35,_⟩ => exact repair12273Cell35
  | ⟨36,_⟩ => exact repair12273Cell36
  | ⟨37,_⟩ => exact repair12273Cell37
  | ⟨38,_⟩ => exact repair12273Cell38
  | ⟨39,_⟩ => exact repair12273Cell39
  | ⟨40,_⟩ => exact repair12273Cell40
  | ⟨41,_⟩ => exact repair12273Cell41
  | ⟨42,_⟩ => exact repair12273Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12273 : FrameRepair 12273 scalarRow12273 where
  cap := cap12273
  cap_nonneg := fun j => (repair12273Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12273])
  endpoint := fun j => (repair12273Cells j).2.1
  endpoint_upper := fun j => (repair12273Cells j).2.2.1
  frame := fun j => (repair12273Cells j).2.2.2

noncomputable def cap12274 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275949019 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (69087993 / 250000000 : ℝ)
  | ⟨2,_⟩ => (276753931 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (69288723 / 250000000 : ℝ)
  | ⟨4,_⟩ => (138777431 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277953843 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (139175681 / 500000000 : ℝ)
  | ⟨7,_⟩ => (2229987 / 8000000 : ℝ)
  | ⟨8,_⟩ => (279144411 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (69884869 / 250000000 : ℝ)
  | ⟨10,_⟩ => (279933569 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (280326213 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (14035919 / 50000000 : ℝ)
  | ⟨13,_⟩ => (2811091 / 10000000 : ℝ)
  | ⟨14,_⟩ => (35187469 / 125000000 : ℝ)
  | ⟨15,_⟩ => (35236163 / 125000000 : ℝ)
  | ⟨16,_⟩ => (282277913 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282665591 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283052329 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283438139 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283823021 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (142103493 / 500000000 : ℝ)
  | ⟨22,_⟩ => (284590027 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (142485829 / 500000000 : ℝ)
  | ⟨24,_⟩ => (2282823 / 8000000 : ℝ)
  | ⟨25,_⟩ => (285732731 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (286112183 / 1000000000 : ℝ)
  | ⟨27,_⟩ => (143245117 / 500000000 : ℝ)
  | ⟨28,_⟩ => (286867389 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287243649 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143809257 / 500000000 : ℝ)
  | ⟨31,_⟩ => (57598599 / 200000000 : ℝ)
  | ⟨32,_⟩ => (144183297 / 500000000 : ℝ)
  | ⟨33,_⟩ => (72184701 / 250000000 : ℝ)
  | ⟨34,_⟩ => (144555069 / 500000000 : ℝ)
  | ⟨35,_⟩ => (1447403 / 5000000 : ℝ)
  | ⟨36,_⟩ => (57970037 / 200000000 : ℝ)
  | ⟨37,_⟩ => (29021891 / 100000000 : ℝ)
  | ⟨38,_⟩ => (29058677 / 100000000 : ℝ)
  | ⟨39,_⟩ => (145476629 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145659443 / 500000000 : ℝ)
  | ⟨41,_⟩ => (291683663 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (73011897 / 250000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12274Cell0 :
    0 ≤ cap12274 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨0,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12274 ⟨0,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨0,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell1 :
    0 ≤ cap12274 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨1,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12274 ⟨1,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨1,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell2 :
    0 ≤ cap12274 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨2,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12274 ⟨2,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨2,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell3 :
    0 ≤ cap12274 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨3,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12274 ⟨3,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨3,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell4 :
    0 ≤ cap12274 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨4,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12274 ⟨4,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨4,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell5 :
    0 ≤ cap12274 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨5,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12274 ⟨5,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨5,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell6 :
    0 ≤ cap12274 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨6,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12274 ⟨6,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨6,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell7 :
    0 ≤ cap12274 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨7,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12274 ⟨7,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨7,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell8 :
    0 ≤ cap12274 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨8,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12274 ⟨8,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨8,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell9 :
    0 ≤ cap12274 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨9,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12274 ⟨9,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨9,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell10 :
    0 ≤ cap12274 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨10,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12274 ⟨10,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨10,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell11 :
    0 ≤ cap12274 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨11,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12274 ⟨11,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨11,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell12 :
    0 ≤ cap12274 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨12,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12274 ⟨12,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨12,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell13 :
    0 ≤ cap12274 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨13,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12274 ⟨13,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨13,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell14 :
    0 ≤ cap12274 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨14,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12274 ⟨14,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨14,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell15 :
    0 ≤ cap12274 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨15,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12274 ⟨15,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨15,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell16 :
    0 ≤ cap12274 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨16,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12274 ⟨16,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨16,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell17 :
    0 ≤ cap12274 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨17,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12274 ⟨17,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨17,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell18 :
    0 ≤ cap12274 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨18,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12274 ⟨18,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨18,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell19 :
    0 ≤ cap12274 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨19,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12274 ⟨19,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨19,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell20 :
    0 ≤ cap12274 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨20,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12274 ⟨20,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨20,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell21 :
    0 ≤ cap12274 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨21,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12274 ⟨21,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨21,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell22 :
    0 ≤ cap12274 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨22,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12274 ⟨22,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨22,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell23 :
    0 ≤ cap12274 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨23,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12274 ⟨23,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨23,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell24 :
    0 ≤ cap12274 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨24,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12274 ⟨24,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨24,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell25 :
    0 ≤ cap12274 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨25,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12274 ⟨25,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨25,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell26 :
    0 ≤ cap12274 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨26,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12274 ⟨26,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨26,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell27 :
    0 ≤ cap12274 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨27,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12274 ⟨27,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨27,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell28 :
    0 ≤ cap12274 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨28,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12274 ⟨28,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨28,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell29 :
    0 ≤ cap12274 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨29,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12274 ⟨29,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨29,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell30 :
    0 ≤ cap12274 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨30,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12274 ⟨30,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨30,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell31 :
    0 ≤ cap12274 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨31,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12274 ⟨31,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨31,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell32 :
    0 ≤ cap12274 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨32,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12274 ⟨32,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨32,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell33 :
    0 ≤ cap12274 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨33,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12274 ⟨33,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨33,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell34 :
    0 ≤ cap12274 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨34,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12274 ⟨34,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨34,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell35 :
    0 ≤ cap12274 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨35,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12274 ⟨35,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨35,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell36 :
    0 ≤ cap12274 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨36,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12274 ⟨36,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨36,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell37 :
    0 ≤ cap12274 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨37,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12274 ⟨37,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨37,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell38 :
    0 ≤ cap12274 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨38,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12274 ⟨38,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨38,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell39 :
    0 ≤ cap12274 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨39,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12274 ⟨39,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨39,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell40 :
    0 ≤ cap12274 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨40,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12274 ⟨40,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨40,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell41 :
    0 ≤ cap12274 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨41,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12274 ⟨41,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨41,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cell42 :
    0 ≤ cap12274 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12274 (parameters ⟨42,by decide⟩)
      (scalarRow12274.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12274 ⟨42,by decide⟩ ∧
    (scalarRow12274.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 ⟨42,by decide⟩ + (scalarRow12274.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12274.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12274.targetFrame := by
  norm_num [cap12274, scalarRow12274, sourceIndex, cell12274, BstLean.Part263.envelope, parameters]

theorem repair12274Cells (j : Fin 43) :
    0 ≤ cap12274 j ∧
    BstLean.Part263.envelope 12274 (parameters j) (scalarRow12274.table (sourceIndex j)).upper ≤ cap12274 j ∧
    (scalarRow12274.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12274 j + (scalarRow12274.table (sourceIndex j)).centre) /
      (scalarRow12274.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12274.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12274Cell0
  | ⟨1,_⟩ => exact repair12274Cell1
  | ⟨2,_⟩ => exact repair12274Cell2
  | ⟨3,_⟩ => exact repair12274Cell3
  | ⟨4,_⟩ => exact repair12274Cell4
  | ⟨5,_⟩ => exact repair12274Cell5
  | ⟨6,_⟩ => exact repair12274Cell6
  | ⟨7,_⟩ => exact repair12274Cell7
  | ⟨8,_⟩ => exact repair12274Cell8
  | ⟨9,_⟩ => exact repair12274Cell9
  | ⟨10,_⟩ => exact repair12274Cell10
  | ⟨11,_⟩ => exact repair12274Cell11
  | ⟨12,_⟩ => exact repair12274Cell12
  | ⟨13,_⟩ => exact repair12274Cell13
  | ⟨14,_⟩ => exact repair12274Cell14
  | ⟨15,_⟩ => exact repair12274Cell15
  | ⟨16,_⟩ => exact repair12274Cell16
  | ⟨17,_⟩ => exact repair12274Cell17
  | ⟨18,_⟩ => exact repair12274Cell18
  | ⟨19,_⟩ => exact repair12274Cell19
  | ⟨20,_⟩ => exact repair12274Cell20
  | ⟨21,_⟩ => exact repair12274Cell21
  | ⟨22,_⟩ => exact repair12274Cell22
  | ⟨23,_⟩ => exact repair12274Cell23
  | ⟨24,_⟩ => exact repair12274Cell24
  | ⟨25,_⟩ => exact repair12274Cell25
  | ⟨26,_⟩ => exact repair12274Cell26
  | ⟨27,_⟩ => exact repair12274Cell27
  | ⟨28,_⟩ => exact repair12274Cell28
  | ⟨29,_⟩ => exact repair12274Cell29
  | ⟨30,_⟩ => exact repair12274Cell30
  | ⟨31,_⟩ => exact repair12274Cell31
  | ⟨32,_⟩ => exact repair12274Cell32
  | ⟨33,_⟩ => exact repair12274Cell33
  | ⟨34,_⟩ => exact repair12274Cell34
  | ⟨35,_⟩ => exact repair12274Cell35
  | ⟨36,_⟩ => exact repair12274Cell36
  | ⟨37,_⟩ => exact repair12274Cell37
  | ⟨38,_⟩ => exact repair12274Cell38
  | ⟨39,_⟩ => exact repair12274Cell39
  | ⟨40,_⟩ => exact repair12274Cell40
  | ⟨41,_⟩ => exact repair12274Cell41
  | ⟨42,_⟩ => exact repair12274Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12274 : FrameRepair 12274 scalarRow12274 where
  cap := cap12274
  cap_nonneg := fun j => (repair12274Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12274])
  endpoint := fun j => (repair12274Cells j).2.1
  endpoint_upper := fun j => (repair12274Cells j).2.2.1
  frame := fun j => (repair12274Cells j).2.2.2


end BstLean.Part264
