import BstLean.Part269Row12350
import BstLean.Part264Repair
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
open BstLean.Part268 (cell12350)
noncomputable def cap12350 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275943303 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (55269153 / 200000000 : ℝ)
  | ⟨2,_⟩ => (138373617 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138573853 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277547189 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277945683 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (69585679 / 250000000 : ℝ)
  | ⟨7,_⟩ => (69684811 / 250000000 : ℝ)
  | ⟨8,_⟩ => (139567399 / 500000000 : ℝ)
  | ⟨9,_⟩ => (279529379 / 1000000000 : ℝ)
  | ⟨10,_⟩ => (279922991 / 1000000000 : ℝ)
  | ⟨11,_⟩ => (56063031 / 200000000 : ℝ)
  | ⟨12,_⟩ => (140353421 / 500000000 : ℝ)
  | ⟨13,_⟩ => (70274271 / 250000000 : ℝ)
  | ⟨14,_⟩ => (140743629 / 500000000 : ℝ)
  | ⟨15,_⟩ => (140938167 / 500000000 : ℝ)
  | ⟨16,_⟩ => (70566117 / 250000000 : ℝ)
  | ⟨17,_⟩ => (282651671 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (17689871 / 62500000 : ℝ)
  | ⟨19,_⟩ => (283423273 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (70951921 / 250000000 : ℝ)
  | ⟨21,_⟩ => (284191179 / 1000000000 : ℝ)
  | ⟨22,_⟩ => (227659 / 800000 : ℝ)
  | ⟨23,_⟩ => (8904841 / 31250000 : ℝ)
  | ⟨24,_⟩ => (142667831 / 500000000 : ℝ)
  | ⟨25,_⟩ => (71428763 / 250000000 : ℝ)
  | ⟨26,_⟩ => (143047019 / 500000000 : ℝ)
  | ⟨27,_⟩ => (2291773 / 8000000 : ℝ)
  | ⟨28,_⟩ => (286848317 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287224113 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (287598517 / 1000000000 : ℝ)
  | ⟨31,_⟩ => (287972537 / 1000000000 : ℝ)
  | ⟨32,_⟩ => (288345677 / 1000000000 : ℝ)
  | ⟨33,_⟩ => (72179357 / 250000000 : ℝ)
  | ⟨34,_⟩ => (18068019 / 62500000 : ℝ)
  | ⟨35,_⟩ => (28945831 / 100000000 : ℝ)
  | ⟨36,_⟩ => (289827439 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (29019571 / 100000000 : ℝ)
  | ⟨38,_⟩ => (72640779 / 250000000 : ℝ)
  | ⟨39,_⟩ => (290929151 / 1000000000 : ℝ)
  | ⟨40,_⟩ => (291294327 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291658653 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (18251383 / 62500000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12350Cell0 :
    0 ≤ cap12350 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨0,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12350 ⟨0,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨0,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell1 :
    0 ≤ cap12350 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨1,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12350 ⟨1,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨1,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell2 :
    0 ≤ cap12350 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨2,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12350 ⟨2,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨2,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell3 :
    0 ≤ cap12350 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨3,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12350 ⟨3,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨3,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell4 :
    0 ≤ cap12350 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨4,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12350 ⟨4,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨4,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell5 :
    0 ≤ cap12350 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨5,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12350 ⟨5,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨5,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell6 :
    0 ≤ cap12350 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨6,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12350 ⟨6,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨6,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell7 :
    0 ≤ cap12350 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨7,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12350 ⟨7,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨7,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell8 :
    0 ≤ cap12350 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨8,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12350 ⟨8,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨8,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell9 :
    0 ≤ cap12350 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨9,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12350 ⟨9,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨9,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell10 :
    0 ≤ cap12350 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨10,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12350 ⟨10,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨10,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell11 :
    0 ≤ cap12350 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨11,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12350 ⟨11,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨11,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell12 :
    0 ≤ cap12350 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨12,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12350 ⟨12,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨12,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell13 :
    0 ≤ cap12350 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨13,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12350 ⟨13,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨13,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell14 :
    0 ≤ cap12350 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨14,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12350 ⟨14,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨14,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell15 :
    0 ≤ cap12350 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨15,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12350 ⟨15,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨15,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell16 :
    0 ≤ cap12350 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨16,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12350 ⟨16,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨16,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell17 :
    0 ≤ cap12350 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨17,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12350 ⟨17,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨17,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell18 :
    0 ≤ cap12350 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨18,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12350 ⟨18,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨18,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell19 :
    0 ≤ cap12350 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨19,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12350 ⟨19,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨19,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell20 :
    0 ≤ cap12350 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨20,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12350 ⟨20,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨20,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell21 :
    0 ≤ cap12350 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨21,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12350 ⟨21,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨21,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell22 :
    0 ≤ cap12350 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨22,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12350 ⟨22,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨22,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell23 :
    0 ≤ cap12350 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨23,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12350 ⟨23,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨23,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell24 :
    0 ≤ cap12350 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨24,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12350 ⟨24,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨24,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell25 :
    0 ≤ cap12350 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨25,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12350 ⟨25,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨25,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell26 :
    0 ≤ cap12350 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨26,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12350 ⟨26,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨26,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell27 :
    0 ≤ cap12350 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨27,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12350 ⟨27,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨27,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell28 :
    0 ≤ cap12350 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨28,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12350 ⟨28,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨28,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell29 :
    0 ≤ cap12350 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨29,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12350 ⟨29,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨29,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell30 :
    0 ≤ cap12350 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨30,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12350 ⟨30,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨30,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell31 :
    0 ≤ cap12350 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨31,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12350 ⟨31,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨31,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell32 :
    0 ≤ cap12350 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨32,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12350 ⟨32,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨32,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell33 :
    0 ≤ cap12350 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨33,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12350 ⟨33,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨33,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell34 :
    0 ≤ cap12350 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨34,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12350 ⟨34,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨34,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell35 :
    0 ≤ cap12350 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨35,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12350 ⟨35,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨35,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell36 :
    0 ≤ cap12350 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨36,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12350 ⟨36,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨36,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell37 :
    0 ≤ cap12350 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨37,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12350 ⟨37,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨37,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell38 :
    0 ≤ cap12350 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨38,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12350 ⟨38,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨38,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell39 :
    0 ≤ cap12350 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨39,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12350 ⟨39,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨39,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell40 :
    0 ≤ cap12350 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨40,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12350 ⟨40,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨40,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell41 :
    0 ≤ cap12350 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨41,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12350 ⟨41,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨41,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cell42 :
    0 ≤ cap12350 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12350 (parameters ⟨42,by decide⟩)
      (scalarRow12350.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12350 ⟨42,by decide⟩ ∧
    (scalarRow12350.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 ⟨42,by decide⟩ + (scalarRow12350.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12350.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12350.targetFrame := by
  norm_num [cap12350, scalarRow12350, sourceIndex, cell12350, BstLean.Part263.envelope, parameters]

theorem repair12350Cells (j : Fin 43) :
    0 ≤ cap12350 j ∧
    BstLean.Part263.envelope 12350 (parameters j) (scalarRow12350.table (sourceIndex j)).upper ≤ cap12350 j ∧
    (scalarRow12350.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12350 j + (scalarRow12350.table (sourceIndex j)).centre) /
      (scalarRow12350.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12350.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12350Cell0
  | ⟨1,_⟩ => exact repair12350Cell1
  | ⟨2,_⟩ => exact repair12350Cell2
  | ⟨3,_⟩ => exact repair12350Cell3
  | ⟨4,_⟩ => exact repair12350Cell4
  | ⟨5,_⟩ => exact repair12350Cell5
  | ⟨6,_⟩ => exact repair12350Cell6
  | ⟨7,_⟩ => exact repair12350Cell7
  | ⟨8,_⟩ => exact repair12350Cell8
  | ⟨9,_⟩ => exact repair12350Cell9
  | ⟨10,_⟩ => exact repair12350Cell10
  | ⟨11,_⟩ => exact repair12350Cell11
  | ⟨12,_⟩ => exact repair12350Cell12
  | ⟨13,_⟩ => exact repair12350Cell13
  | ⟨14,_⟩ => exact repair12350Cell14
  | ⟨15,_⟩ => exact repair12350Cell15
  | ⟨16,_⟩ => exact repair12350Cell16
  | ⟨17,_⟩ => exact repair12350Cell17
  | ⟨18,_⟩ => exact repair12350Cell18
  | ⟨19,_⟩ => exact repair12350Cell19
  | ⟨20,_⟩ => exact repair12350Cell20
  | ⟨21,_⟩ => exact repair12350Cell21
  | ⟨22,_⟩ => exact repair12350Cell22
  | ⟨23,_⟩ => exact repair12350Cell23
  | ⟨24,_⟩ => exact repair12350Cell24
  | ⟨25,_⟩ => exact repair12350Cell25
  | ⟨26,_⟩ => exact repair12350Cell26
  | ⟨27,_⟩ => exact repair12350Cell27
  | ⟨28,_⟩ => exact repair12350Cell28
  | ⟨29,_⟩ => exact repair12350Cell29
  | ⟨30,_⟩ => exact repair12350Cell30
  | ⟨31,_⟩ => exact repair12350Cell31
  | ⟨32,_⟩ => exact repair12350Cell32
  | ⟨33,_⟩ => exact repair12350Cell33
  | ⟨34,_⟩ => exact repair12350Cell34
  | ⟨35,_⟩ => exact repair12350Cell35
  | ⟨36,_⟩ => exact repair12350Cell36
  | ⟨37,_⟩ => exact repair12350Cell37
  | ⟨38,_⟩ => exact repair12350Cell38
  | ⟨39,_⟩ => exact repair12350Cell39
  | ⟨40,_⟩ => exact repair12350Cell40
  | ⟨41,_⟩ => exact repair12350Cell41
  | ⟨42,_⟩ => exact repair12350Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12350 : FrameRepair 12350 scalarRow12350 where
  cap := cap12350
  cap_nonneg := fun j => (repair12350Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12350])
  endpoint := fun j => (repair12350Cells j).2.1
  endpoint_upper := fun j => (repair12350Cells j).2.2.1
  frame := fun j => (repair12350Cells j).2.2.2

end BstLean.Part269
