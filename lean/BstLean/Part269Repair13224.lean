import BstLean.Part269Row13224
import BstLean.Part264Repair
namespace BstLean.Part269
open Real Set BstLean.Part255 BstLean.Part263 BstLean.Part264
open BstLean.Part269 (cell13224)
noncomputable def cap13224 : Fin 43 → ℝ
  | ⟨0,_⟩ => (275881269 / 1000000000 : ℝ)
  | ⟨1,_⟩ => (276278401 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (276674551 / 1000000000 : ℝ)
  | ⟨3,_⟩ => (69267429 / 250000000 : ℝ)
  | ⟨4,_⟩ => (138731951 / 500000000 : ℝ)
  | ⟨5,_⟩ => (277857111 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (278248871 / 1000000000 : ℝ)
  | ⟨7,_⟩ => (34830017 / 125000000 : ℝ)
  | ⟨8,_⟩ => (139515219 / 500000000 : ℝ)
  | ⟨9,_⟩ => (13970989 / 50000000 : ℝ)
  | ⟨10,_⟩ => (139904081 / 500000000 : ℝ)
  | ⟨11,_⟩ => (280195109 / 1000000000 : ℝ)
  | ⟨12,_⟩ => (280581589 / 1000000000 : ℝ)
  | ⟨13,_⟩ => (140483317 / 500000000 : ℝ)
  | ⟨14,_⟩ => (35168953 / 125000000 : ℝ)
  | ⟨15,_⟩ => (140867763 / 500000000 : ℝ)
  | ⟨16,_⟩ => (8816203 / 31250000 : ℝ)
  | ⟨17,_⟩ => (282500547 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (282881671 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (141630939 / 500000000 : ℝ)
  | ⟨20,_⟩ => (283641169 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (56803911 / 200000000 : ℝ)
  | ⟨22,_⟩ => (284397029 / 1000000000 : ℝ)
  | ⟨23,_⟩ => (17798319 / 62500000 : ℝ)
  | ⟨24,_⟩ => (285148777 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (285523101 / 1000000000 : ℝ)
  | ⟨26,_⟩ => (35737129 / 125000000 : ℝ)
  | ⟨27,_⟩ => (11450783 / 40000000 : ℝ)
  | ⟨28,_⟩ => (286641233 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (143506003 / 500000000 : ℝ)
  | ⟨30,_⟩ => (143690699 / 500000000 : ℝ)
  | ⟨31,_⟩ => (17984401 / 62500000 : ℝ)
  | ⟨32,_⟩ => (57623713 / 200000000 : ℝ)
  | ⟨33,_⟩ => (57697067 / 200000000 : ℝ)
  | ⟨34,_⟩ => (288851241 / 1000000000 : ℝ)
  | ⟨35,_⟩ => (289216287 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (289580467 / 1000000000 : ℝ)
  | ⟨37,_⟩ => (289943799 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (290306277 / 1000000000 : ℝ)
  | ⟨39,_⟩ => (145333697 / 500000000 : ℝ)
  | ⟨40,_⟩ => (291027663 / 1000000000 : ℝ)
  | ⟨41,_⟩ => (291387091 / 1000000000 : ℝ)
  | ⟨42,_⟩ => (291745679 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair13224Cell0 :
    0 ≤ cap13224 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨0,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap13224 ⟨0,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨0,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell1 :
    0 ≤ cap13224 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨1,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap13224 ⟨1,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨1,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell2 :
    0 ≤ cap13224 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨2,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap13224 ⟨2,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨2,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell3 :
    0 ≤ cap13224 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨3,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap13224 ⟨3,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨3,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell4 :
    0 ≤ cap13224 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨4,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap13224 ⟨4,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨4,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell5 :
    0 ≤ cap13224 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨5,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap13224 ⟨5,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨5,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell6 :
    0 ≤ cap13224 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨6,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap13224 ⟨6,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨6,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell7 :
    0 ≤ cap13224 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨7,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap13224 ⟨7,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨7,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell8 :
    0 ≤ cap13224 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨8,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap13224 ⟨8,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨8,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell9 :
    0 ≤ cap13224 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨9,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap13224 ⟨9,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨9,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell10 :
    0 ≤ cap13224 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨10,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap13224 ⟨10,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨10,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell11 :
    0 ≤ cap13224 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨11,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap13224 ⟨11,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨11,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell12 :
    0 ≤ cap13224 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨12,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap13224 ⟨12,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨12,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell13 :
    0 ≤ cap13224 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨13,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap13224 ⟨13,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨13,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell14 :
    0 ≤ cap13224 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨14,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap13224 ⟨14,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨14,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell15 :
    0 ≤ cap13224 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨15,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap13224 ⟨15,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨15,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell16 :
    0 ≤ cap13224 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨16,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap13224 ⟨16,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨16,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell17 :
    0 ≤ cap13224 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨17,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap13224 ⟨17,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨17,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell18 :
    0 ≤ cap13224 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨18,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap13224 ⟨18,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨18,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell19 :
    0 ≤ cap13224 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨19,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap13224 ⟨19,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨19,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell20 :
    0 ≤ cap13224 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨20,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap13224 ⟨20,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨20,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell21 :
    0 ≤ cap13224 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨21,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap13224 ⟨21,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨21,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell22 :
    0 ≤ cap13224 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨22,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap13224 ⟨22,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨22,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell23 :
    0 ≤ cap13224 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨23,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap13224 ⟨23,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨23,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell24 :
    0 ≤ cap13224 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨24,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap13224 ⟨24,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨24,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell25 :
    0 ≤ cap13224 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨25,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap13224 ⟨25,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨25,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell26 :
    0 ≤ cap13224 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨26,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap13224 ⟨26,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨26,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell27 :
    0 ≤ cap13224 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨27,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap13224 ⟨27,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨27,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell28 :
    0 ≤ cap13224 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨28,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap13224 ⟨28,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨28,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell29 :
    0 ≤ cap13224 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨29,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap13224 ⟨29,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨29,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell30 :
    0 ≤ cap13224 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨30,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap13224 ⟨30,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨30,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell31 :
    0 ≤ cap13224 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨31,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap13224 ⟨31,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨31,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell32 :
    0 ≤ cap13224 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨32,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap13224 ⟨32,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨32,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell33 :
    0 ≤ cap13224 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨33,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap13224 ⟨33,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨33,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell34 :
    0 ≤ cap13224 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨34,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap13224 ⟨34,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨34,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell35 :
    0 ≤ cap13224 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨35,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap13224 ⟨35,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨35,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell36 :
    0 ≤ cap13224 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨36,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap13224 ⟨36,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨36,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell37 :
    0 ≤ cap13224 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨37,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap13224 ⟨37,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨37,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell38 :
    0 ≤ cap13224 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨38,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap13224 ⟨38,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨38,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell39 :
    0 ≤ cap13224 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨39,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap13224 ⟨39,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨39,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell40 :
    0 ≤ cap13224 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨40,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap13224 ⟨40,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨40,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell41 :
    0 ≤ cap13224 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨41,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap13224 ⟨41,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨41,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cell42 :
    0 ≤ cap13224 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 13224 (parameters ⟨42,by decide⟩)
      (scalarRow13224.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap13224 ⟨42,by decide⟩ ∧
    (scalarRow13224.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 ⟨42,by decide⟩ + (scalarRow13224.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow13224.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow13224.targetFrame := by
  norm_num [cap13224, scalarRow13224, sourceIndex, cell13224, BstLean.Part263.envelope, parameters]

theorem repair13224Cells (j : Fin 43) :
    0 ≤ cap13224 j ∧
    BstLean.Part263.envelope 13224 (parameters j) (scalarRow13224.table (sourceIndex j)).upper ≤ cap13224 j ∧
    (scalarRow13224.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap13224 j + (scalarRow13224.table (sourceIndex j)).centre) /
      (scalarRow13224.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow13224.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair13224Cell0
  | ⟨1,_⟩ => exact repair13224Cell1
  | ⟨2,_⟩ => exact repair13224Cell2
  | ⟨3,_⟩ => exact repair13224Cell3
  | ⟨4,_⟩ => exact repair13224Cell4
  | ⟨5,_⟩ => exact repair13224Cell5
  | ⟨6,_⟩ => exact repair13224Cell6
  | ⟨7,_⟩ => exact repair13224Cell7
  | ⟨8,_⟩ => exact repair13224Cell8
  | ⟨9,_⟩ => exact repair13224Cell9
  | ⟨10,_⟩ => exact repair13224Cell10
  | ⟨11,_⟩ => exact repair13224Cell11
  | ⟨12,_⟩ => exact repair13224Cell12
  | ⟨13,_⟩ => exact repair13224Cell13
  | ⟨14,_⟩ => exact repair13224Cell14
  | ⟨15,_⟩ => exact repair13224Cell15
  | ⟨16,_⟩ => exact repair13224Cell16
  | ⟨17,_⟩ => exact repair13224Cell17
  | ⟨18,_⟩ => exact repair13224Cell18
  | ⟨19,_⟩ => exact repair13224Cell19
  | ⟨20,_⟩ => exact repair13224Cell20
  | ⟨21,_⟩ => exact repair13224Cell21
  | ⟨22,_⟩ => exact repair13224Cell22
  | ⟨23,_⟩ => exact repair13224Cell23
  | ⟨24,_⟩ => exact repair13224Cell24
  | ⟨25,_⟩ => exact repair13224Cell25
  | ⟨26,_⟩ => exact repair13224Cell26
  | ⟨27,_⟩ => exact repair13224Cell27
  | ⟨28,_⟩ => exact repair13224Cell28
  | ⟨29,_⟩ => exact repair13224Cell29
  | ⟨30,_⟩ => exact repair13224Cell30
  | ⟨31,_⟩ => exact repair13224Cell31
  | ⟨32,_⟩ => exact repair13224Cell32
  | ⟨33,_⟩ => exact repair13224Cell33
  | ⟨34,_⟩ => exact repair13224Cell34
  | ⟨35,_⟩ => exact repair13224Cell35
  | ⟨36,_⟩ => exact repair13224Cell36
  | ⟨37,_⟩ => exact repair13224Cell37
  | ⟨38,_⟩ => exact repair13224Cell38
  | ⟨39,_⟩ => exact repair13224Cell39
  | ⟨40,_⟩ => exact repair13224Cell40
  | ⟨41,_⟩ => exact repair13224Cell41
  | ⟨42,_⟩ => exact repair13224Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair13224 : FrameRepair 13224 scalarRow13224 where
  cap := cap13224
  cap_nonneg := fun j => (repair13224Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap13224])
  endpoint := fun j => (repair13224Cells j).2.1
  endpoint_upper := fun j => (repair13224Cells j).2.2.1
  frame := fun j => (repair13224Cells j).2.2.2

end BstLean.Part269
