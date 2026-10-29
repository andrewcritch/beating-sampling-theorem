import BstLean.Part264Repair
/-! Rational envelope and frame checks for each dimension. -/
namespace BstLean.Part264
open Real Set BstLean.Part255 BstLean.Part263
noncomputable def cap12226 : Fin 43 → ℝ
  | ⟨0,_⟩ => (137976329 / 500000000 : ℝ)
  | ⟨1,_⟩ => (276355923 / 1000000000 : ℝ)
  | ⟨2,_⟩ => (138379097 / 500000000 : ℝ)
  | ⟨3,_⟩ => (138579733 / 500000000 : ℝ)
  | ⟨4,_⟩ => (277559747 / 1000000000 : ℝ)
  | ⟨5,_⟩ => (277959037 / 1000000000 : ℝ)
  | ⟨6,_⟩ => (55671373 / 200000000 : ℝ)
  | ⟨7,_⟩ => (139377093 / 500000000 : ℝ)
  | ⟨8,_⟩ => (279150531 / 1000000000 : ℝ)
  | ⟨9,_⟩ => (139772951 / 500000000 : ℝ)
  | ⟨10,_⟩ => (139970151 / 500000000 : ℝ)
  | ⟨11,_⟩ => (70083313 / 250000000 : ℝ)
  | ⟨12,_⟩ => (70181431 / 250000000 : ℝ)
  | ⟨13,_⟩ => (70279187 / 250000000 : ℝ)
  | ⟨14,_⟩ => (35188463 / 125000000 : ℝ)
  | ⟨15,_⟩ => (7047439 / 25000000 : ℝ)
  | ⟨16,_⟩ => (282286471 / 1000000000 : ℝ)
  | ⟨17,_⟩ => (282674451 / 1000000000 : ℝ)
  | ⟨18,_⟩ => (283061491 / 1000000000 : ℝ)
  | ⟨19,_⟩ => (283447601 / 1000000000 : ℝ)
  | ⟨20,_⟩ => (283832783 / 1000000000 : ℝ)
  | ⟨21,_⟩ => (35527131 / 125000000 : ℝ)
  | ⟨22,_⟩ => (71150097 / 250000000 : ℝ)
  | ⟨23,_⟩ => (71245579 / 250000000 : ℝ)
  | ⟨24,_⟩ => (285363831 / 1000000000 : ℝ)
  | ⟨25,_⟩ => (17858999 / 62500000 : ℝ)
  | ⟨26,_⟩ => (71530933 / 250000000 : ℝ)
  | ⟨27,_⟩ => (286502079 / 1000000000 : ℝ)
  | ⟨28,_⟩ => (286879529 / 1000000000 : ℝ)
  | ⟨29,_⟩ => (287256083 / 1000000000 : ℝ)
  | ⟨30,_⟩ => (143815621 / 500000000 : ℝ)
  | ⟨31,_⟩ => (2250047 / 7812500 : ℝ)
  | ⟨32,_⟩ => (72094977 / 250000000 : ℝ)
  | ⟨33,_⟩ => (288752409 / 1000000000 : ℝ)
  | ⟨34,_⟩ => (144562017 / 500000000 : ℝ)
  | ⟨35,_⟩ => (289494787 / 1000000000 : ℝ)
  | ⟨36,_⟩ => (144932331 / 500000000 : ℝ)
  | ⟨37,_⟩ => (290233677 / 1000000000 : ℝ)
  | ⟨38,_⟩ => (145300913 / 500000000 : ℝ)
  | ⟨39,_⟩ => (145484301 / 500000000 : ℝ)
  | ⟨40,_⟩ => (145667259 / 500000000 : ℝ)
  | ⟨41,_⟩ => (145849791 / 500000000 : ℝ)
  | ⟨42,_⟩ => (292063793 / 1000000000 : ℝ)
  | ⟨j+43,h⟩ => False.elim (by omega)

theorem repair12226Cell0 :
    0 ≤ cap12226 ⟨0,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨0,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨0,by decide⟩)).upper ≤ cap12226 ⟨0,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨0,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨0,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨0,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨0,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell1 :
    0 ≤ cap12226 ⟨1,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨1,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨1,by decide⟩)).upper ≤ cap12226 ⟨1,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨1,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨1,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨1,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨1,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell2 :
    0 ≤ cap12226 ⟨2,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨2,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨2,by decide⟩)).upper ≤ cap12226 ⟨2,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨2,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨2,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨2,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨2,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell3 :
    0 ≤ cap12226 ⟨3,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨3,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨3,by decide⟩)).upper ≤ cap12226 ⟨3,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨3,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨3,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨3,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨3,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell4 :
    0 ≤ cap12226 ⟨4,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨4,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨4,by decide⟩)).upper ≤ cap12226 ⟨4,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨4,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨4,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨4,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨4,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell5 :
    0 ≤ cap12226 ⟨5,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨5,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨5,by decide⟩)).upper ≤ cap12226 ⟨5,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨5,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨5,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨5,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨5,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell6 :
    0 ≤ cap12226 ⟨6,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨6,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨6,by decide⟩)).upper ≤ cap12226 ⟨6,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨6,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨6,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨6,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨6,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell7 :
    0 ≤ cap12226 ⟨7,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨7,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨7,by decide⟩)).upper ≤ cap12226 ⟨7,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨7,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨7,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨7,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨7,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell8 :
    0 ≤ cap12226 ⟨8,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨8,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨8,by decide⟩)).upper ≤ cap12226 ⟨8,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨8,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨8,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨8,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨8,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell9 :
    0 ≤ cap12226 ⟨9,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨9,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨9,by decide⟩)).upper ≤ cap12226 ⟨9,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨9,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨9,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨9,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨9,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell10 :
    0 ≤ cap12226 ⟨10,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨10,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨10,by decide⟩)).upper ≤ cap12226 ⟨10,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨10,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨10,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨10,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨10,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell11 :
    0 ≤ cap12226 ⟨11,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨11,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨11,by decide⟩)).upper ≤ cap12226 ⟨11,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨11,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨11,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨11,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨11,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell12 :
    0 ≤ cap12226 ⟨12,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨12,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨12,by decide⟩)).upper ≤ cap12226 ⟨12,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨12,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨12,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨12,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨12,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell13 :
    0 ≤ cap12226 ⟨13,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨13,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨13,by decide⟩)).upper ≤ cap12226 ⟨13,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨13,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨13,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨13,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨13,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell14 :
    0 ≤ cap12226 ⟨14,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨14,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨14,by decide⟩)).upper ≤ cap12226 ⟨14,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨14,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨14,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨14,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨14,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell15 :
    0 ≤ cap12226 ⟨15,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨15,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨15,by decide⟩)).upper ≤ cap12226 ⟨15,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨15,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨15,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨15,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨15,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell16 :
    0 ≤ cap12226 ⟨16,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨16,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨16,by decide⟩)).upper ≤ cap12226 ⟨16,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨16,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨16,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨16,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨16,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell17 :
    0 ≤ cap12226 ⟨17,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨17,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨17,by decide⟩)).upper ≤ cap12226 ⟨17,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨17,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨17,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨17,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨17,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell18 :
    0 ≤ cap12226 ⟨18,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨18,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨18,by decide⟩)).upper ≤ cap12226 ⟨18,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨18,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨18,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨18,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨18,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell19 :
    0 ≤ cap12226 ⟨19,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨19,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨19,by decide⟩)).upper ≤ cap12226 ⟨19,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨19,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨19,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨19,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨19,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell20 :
    0 ≤ cap12226 ⟨20,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨20,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨20,by decide⟩)).upper ≤ cap12226 ⟨20,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨20,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨20,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨20,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨20,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell21 :
    0 ≤ cap12226 ⟨21,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨21,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨21,by decide⟩)).upper ≤ cap12226 ⟨21,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨21,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨21,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨21,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨21,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell22 :
    0 ≤ cap12226 ⟨22,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨22,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨22,by decide⟩)).upper ≤ cap12226 ⟨22,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨22,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨22,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨22,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨22,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell23 :
    0 ≤ cap12226 ⟨23,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨23,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨23,by decide⟩)).upper ≤ cap12226 ⟨23,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨23,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨23,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨23,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨23,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell24 :
    0 ≤ cap12226 ⟨24,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨24,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨24,by decide⟩)).upper ≤ cap12226 ⟨24,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨24,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨24,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨24,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨24,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell25 :
    0 ≤ cap12226 ⟨25,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨25,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨25,by decide⟩)).upper ≤ cap12226 ⟨25,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨25,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨25,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨25,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨25,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell26 :
    0 ≤ cap12226 ⟨26,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨26,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨26,by decide⟩)).upper ≤ cap12226 ⟨26,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨26,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨26,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨26,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨26,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell27 :
    0 ≤ cap12226 ⟨27,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨27,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨27,by decide⟩)).upper ≤ cap12226 ⟨27,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨27,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨27,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨27,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨27,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell28 :
    0 ≤ cap12226 ⟨28,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨28,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨28,by decide⟩)).upper ≤ cap12226 ⟨28,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨28,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨28,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨28,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨28,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell29 :
    0 ≤ cap12226 ⟨29,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨29,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨29,by decide⟩)).upper ≤ cap12226 ⟨29,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨29,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨29,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨29,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨29,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell30 :
    0 ≤ cap12226 ⟨30,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨30,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨30,by decide⟩)).upper ≤ cap12226 ⟨30,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨30,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨30,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨30,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨30,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell31 :
    0 ≤ cap12226 ⟨31,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨31,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨31,by decide⟩)).upper ≤ cap12226 ⟨31,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨31,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨31,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨31,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨31,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell32 :
    0 ≤ cap12226 ⟨32,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨32,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨32,by decide⟩)).upper ≤ cap12226 ⟨32,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨32,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨32,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨32,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨32,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell33 :
    0 ≤ cap12226 ⟨33,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨33,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨33,by decide⟩)).upper ≤ cap12226 ⟨33,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨33,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨33,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨33,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨33,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell34 :
    0 ≤ cap12226 ⟨34,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨34,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨34,by decide⟩)).upper ≤ cap12226 ⟨34,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨34,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨34,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨34,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨34,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell35 :
    0 ≤ cap12226 ⟨35,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨35,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨35,by decide⟩)).upper ≤ cap12226 ⟨35,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨35,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨35,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨35,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨35,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell36 :
    0 ≤ cap12226 ⟨36,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨36,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨36,by decide⟩)).upper ≤ cap12226 ⟨36,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨36,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨36,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨36,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨36,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell37 :
    0 ≤ cap12226 ⟨37,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨37,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨37,by decide⟩)).upper ≤ cap12226 ⟨37,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨37,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨37,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨37,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨37,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell38 :
    0 ≤ cap12226 ⟨38,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨38,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨38,by decide⟩)).upper ≤ cap12226 ⟨38,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨38,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨38,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨38,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨38,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell39 :
    0 ≤ cap12226 ⟨39,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨39,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨39,by decide⟩)).upper ≤ cap12226 ⟨39,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨39,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨39,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨39,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨39,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell40 :
    0 ≤ cap12226 ⟨40,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨40,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨40,by decide⟩)).upper ≤ cap12226 ⟨40,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨40,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨40,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨40,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨40,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell41 :
    0 ≤ cap12226 ⟨41,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨41,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨41,by decide⟩)).upper ≤ cap12226 ⟨41,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨41,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨41,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨41,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨41,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cell42 :
    0 ≤ cap12226 ⟨42,by decide⟩ ∧
    BstLean.Part263.envelope 12226 (parameters ⟨42,by decide⟩)
      (scalarRow12226.table (sourceIndex ⟨42,by decide⟩)).upper ≤ cap12226 ⟨42,by decide⟩ ∧
    (scalarRow12226.table (sourceIndex ⟨42,by decide⟩)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 ⟨42,by decide⟩ + (scalarRow12226.table (sourceIndex ⟨42,by decide⟩)).centre) /
      (scalarRow12226.table (sourceIndex ⟨42,by decide⟩)).cutoff + 11 / 1000 ≤
      scalarRow12226.targetFrame := by
  norm_num [cap12226, scalarRow12226, sourceIndex, cell12226, BstLean.Part263.envelope, parameters]

theorem repair12226Cells (j : Fin 43) :
    0 ≤ cap12226 j ∧
    BstLean.Part263.envelope 12226 (parameters j) (scalarRow12226.table (sourceIndex j)).upper ≤ cap12226 j ∧
    (scalarRow12226.table (sourceIndex j)).upper ≤ (528 / 1000 : ℝ) ∧
    (cap12226 j + (scalarRow12226.table (sourceIndex j)).centre) /
      (scalarRow12226.table (sourceIndex j)).cutoff + 11 / 1000 ≤ scalarRow12226.targetFrame := by
  match j with
  | ⟨0,_⟩ => exact repair12226Cell0
  | ⟨1,_⟩ => exact repair12226Cell1
  | ⟨2,_⟩ => exact repair12226Cell2
  | ⟨3,_⟩ => exact repair12226Cell3
  | ⟨4,_⟩ => exact repair12226Cell4
  | ⟨5,_⟩ => exact repair12226Cell5
  | ⟨6,_⟩ => exact repair12226Cell6
  | ⟨7,_⟩ => exact repair12226Cell7
  | ⟨8,_⟩ => exact repair12226Cell8
  | ⟨9,_⟩ => exact repair12226Cell9
  | ⟨10,_⟩ => exact repair12226Cell10
  | ⟨11,_⟩ => exact repair12226Cell11
  | ⟨12,_⟩ => exact repair12226Cell12
  | ⟨13,_⟩ => exact repair12226Cell13
  | ⟨14,_⟩ => exact repair12226Cell14
  | ⟨15,_⟩ => exact repair12226Cell15
  | ⟨16,_⟩ => exact repair12226Cell16
  | ⟨17,_⟩ => exact repair12226Cell17
  | ⟨18,_⟩ => exact repair12226Cell18
  | ⟨19,_⟩ => exact repair12226Cell19
  | ⟨20,_⟩ => exact repair12226Cell20
  | ⟨21,_⟩ => exact repair12226Cell21
  | ⟨22,_⟩ => exact repair12226Cell22
  | ⟨23,_⟩ => exact repair12226Cell23
  | ⟨24,_⟩ => exact repair12226Cell24
  | ⟨25,_⟩ => exact repair12226Cell25
  | ⟨26,_⟩ => exact repair12226Cell26
  | ⟨27,_⟩ => exact repair12226Cell27
  | ⟨28,_⟩ => exact repair12226Cell28
  | ⟨29,_⟩ => exact repair12226Cell29
  | ⟨30,_⟩ => exact repair12226Cell30
  | ⟨31,_⟩ => exact repair12226Cell31
  | ⟨32,_⟩ => exact repair12226Cell32
  | ⟨33,_⟩ => exact repair12226Cell33
  | ⟨34,_⟩ => exact repair12226Cell34
  | ⟨35,_⟩ => exact repair12226Cell35
  | ⟨36,_⟩ => exact repair12226Cell36
  | ⟨37,_⟩ => exact repair12226Cell37
  | ⟨38,_⟩ => exact repair12226Cell38
  | ⟨39,_⟩ => exact repair12226Cell39
  | ⟨40,_⟩ => exact repair12226Cell40
  | ⟨41,_⟩ => exact repair12226Cell41
  | ⟨42,_⟩ => exact repair12226Cell42
  | ⟨j+43,h⟩ => exact False.elim (by omega)

noncomputable def repair12226 : FrameRepair 12226 scalarRow12226 where
  cap := cap12226
  cap_nonneg := fun j => (repair12226Cells j).1
  cap_mono := Fin.monotone_iff_le_succ.mpr (by
    intro j
    fin_cases j <;> norm_num [cap12226])
  endpoint := fun j => (repair12226Cells j).2.1
  endpoint_upper := fun j => (repair12226Cells j).2.2.1
  frame := fun j => (repair12226Cells j).2.2.2


end BstLean.Part264
